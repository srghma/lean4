// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char
// Imports: Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_nat_dec_lt, lean_string_push, lean_uint32_add,
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint32_dec_lt, lean_uint32_to_nat, lean_usize_add,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Prelude::l_Char_ofNat;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_isApp, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_isConstOf, l_Lean_eagerReflBoolTrue, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkRawNatLit, l_Lean_mkStrLit,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_Level_succ___override};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getCharValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::UInt::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Util::l_Lean_Meta_Simp_evalPropStep___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    l_Lean_Meta_Simp_addSEvalprocBuiltinAttr, l_Lean_Meta_Simp_addSimprocBuiltinAttr,
    l_Lean_Meta_Simp_registerBuiltinDSimproc, l_Lean_Meta_Simp_registerBuiltinSimproc,
};
pub static l_Char_reduceUnary___redArg___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Char_reduceUnary___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceUnary___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceBinPred___redArg___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Char_reduceBinPred___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBinPred___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceBoolPred___redArg___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Char_reduceBoolPred___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceBoolPred___redArg___closed__1_value: leanh::LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Char_reduceBoolPred___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceBoolPred___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceBoolPred___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            15761733860085307253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceBoolPred___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Char_reduceBoolPred___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceBoolPred___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Char_reduceBoolPred___redArg___closed__4_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Char_reduceBoolPred___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static l_Char_reduceBoolPred___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceBoolPred___redArg___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            9255189395584251158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceBoolPred___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBoolPred___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Char_reduceBoolPred___redArg___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceBoolPred___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Char_reduceToLower___redArg___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [67, 104, 97, 114, 0],
    };
static mut l_Char_reduceToLower___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceToLower___redArg___closed__1_value: leanh::LeanStringObject<8> =
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
        m_data: [116, 111, 76, 111, 119, 101, 114, 0],
    };
static mut l_Char_reduceToLower___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceToLower___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceToLower___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            5960260352514745136 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceToLower___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceToLower___redArg___closed__3_value: leanh::LeanStringObject<6> =
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
        m_data: [111, 102, 78, 97, 116, 0],
    };
static mut l_Char_reduceToLower___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static l_Char_reduceToLower___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceToLower___redArg___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            18098914779984442139 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceToLower___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Char_reduceToLower___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceToLower___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 84, 111, 76, 111, 119, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value) as *mut leanh::LeanObject,14890195885584917750 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__2_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceToUpper___redArg___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [116, 111, 85, 112, 112, 101, 114, 0],
    };
static mut l_Char_reduceToUpper___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToUpper___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceToUpper___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceToUpper___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToUpper___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceToUpper___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            6419501434565500898 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceToUpper___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToUpper___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 84, 111, 85, 112, 112, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value) as *mut leanh::LeanObject,18055566343467141139 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceToUpper___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceToNat___redArg___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [116, 111, 78, 97, 116, 0],
    };
static mut l_Char_reduceToNat___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToNat___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceToNat___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceToNat___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToNat___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceToNat___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            5008959047061076168 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceToNat___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToNat___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [114, 101, 100, 117, 99, 101, 84, 111, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value) as *mut leanh::LeanObject,9678780480894890565 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceToNat___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceIsWhitespace___redArg___closed__0_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [105, 115, 87, 104, 105, 116, 101, 115, 112, 97, 99, 101, 0],
};
static mut l_Char_reduceIsWhitespace___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsWhitespace___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceIsWhitespace___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceIsWhitespace___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceIsWhitespace___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceIsWhitespace___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            6312648028002043587 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceIsWhitespace___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsWhitespace___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [114, 101, 100, 117, 99, 101, 73, 115, 87, 104, 105, 116, 101, 115, 112, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value) as *mut leanh::LeanObject,4248518697882731144 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceIsWhitespace___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceIsUpper___redArg___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [105, 115, 85, 112, 112, 101, 114, 0],
    };
static mut l_Char_reduceIsUpper___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsUpper___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceIsUpper___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceIsUpper___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceIsUpper___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceIsUpper___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            13044655891740489673 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceIsUpper___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsUpper___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 73, 115, 85, 112, 112, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value) as *mut leanh::LeanObject,7474988579100713264 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceIsUpper___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceIsLower___redArg___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [105, 115, 76, 111, 119, 101, 114, 0],
    };
static mut l_Char_reduceIsLower___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsLower___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceIsLower___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceIsLower___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceIsLower___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceIsLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            17731702160483239045 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceIsLower___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsLower___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 73, 115, 76, 111, 119, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value) as *mut leanh::LeanObject,9937587701555167914 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceIsLower___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceIsAlpha___redArg___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [105, 115, 65, 108, 112, 104, 97, 0],
    };
static mut l_Char_reduceIsAlpha___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsAlpha___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceIsAlpha___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceIsAlpha___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceIsAlpha___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceIsAlpha___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            3587489532296894979 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceIsAlpha___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsAlpha___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 73, 115, 65, 108, 112, 104, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value) as *mut leanh::LeanObject,8976774782029705931 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceIsAlpha___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceIsDigit___redArg___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [105, 115, 68, 105, 103, 105, 116, 0],
    };
static mut l_Char_reduceIsDigit___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsDigit___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceIsDigit___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceIsDigit___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceIsDigit___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceIsDigit___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            11432710341194548027 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceIsDigit___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsDigit___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 73, 115, 68, 105, 103, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value) as *mut leanh::LeanObject,1385939871787622098 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceIsDigit___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceIsAlphaNum___redArg___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [105, 115, 65, 108, 112, 104, 97, 110, 117, 109, 0],
    };
static mut l_Char_reduceIsAlphaNum___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsAlphaNum___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceIsAlphaNum___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceIsAlphaNum___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceIsAlphaNum___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceIsAlphaNum___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            6304998854730759479 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceIsAlphaNum___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceIsAlphaNum___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [114, 101, 100, 117, 99, 101, 73, 115, 65, 108, 112, 104, 97, 78, 117, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value) as *mut leanh::LeanObject,17049084312306264412 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceIsAlphaNum___redArg___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceToString___redArg___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [84, 111, 83, 116, 114, 105, 110, 103, 0],
    };
static mut l_Char_reduceToString___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToString___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceToString___redArg___closed__1_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 111, 83, 116, 114, 105, 110, 103, 0],
    };
static mut l_Char_reduceToString___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToString___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceToString___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToString___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            12150634900968360478 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceToString___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToString___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceToString___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            7720788540864844494 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceToString___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToString___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceToString___redArg___closed__3_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Char_reduceToString___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceToString___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [114, 101, 100, 117, 99, 101, 84, 111, 83, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,11693491960767348302 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceToString___redArg___closed__2_value) as *mut leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value: leanh::LeanArrayObject<4> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceVal___redArg___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [118, 97, 108, 0],
    };
static mut l_Char_reduceVal___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceVal___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceVal___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            9449710148530370881 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceVal___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceVal___redArg___closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [79, 102, 78, 97, 116, 0],
    };
static mut l_Char_reduceVal___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static l_Char_reduceVal___redArg___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            17636616155771105671 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceVal___redArg___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            15578568367168711682 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceVal___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Char_reduceVal___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceVal___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_reduceVal___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceVal___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_reduceVal___redArg___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceVal___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Char_reduceVal___redArg___closed__7_value: leanh::LeanStringObject<7> =
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
        m_data: [85, 73, 110, 116, 51, 50, 0],
    };
static mut l_Char_reduceVal___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceVal___redArg___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            13474504806189678690 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceVal___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Char_reduceVal___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceVal___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Char_reduceVal___redArg___closed__10_value: leanh::LeanStringObject<10> =
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
        m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 0],
    };
static mut l_Char_reduceVal___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__10_value)
        as *mut leanh::LeanObject;
static l_Char_reduceVal___redArg___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            13474504806189678690 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceVal___redArg___closed__11_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__10_value)
                as *mut leanh::LeanObject,
            16173759620455419504 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceVal___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceVal___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Char_reduceVal___redArg___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceVal___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 86, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value) as *mut leanh::LeanObject,559799124173221597 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 6 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceLT___redArg___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [76, 84, 0],
    };
static mut l_Char_reduceLT___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceLT___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceLT___redArg___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [108, 116, 0],
    };
static mut l_Char_reduceLT___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceLT___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceLT___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceLT___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            17878876274162330439 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceLT___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceLT___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceLT___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            11833570877100518198 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceLT___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceLT___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value) as *mut leanh::LeanObject,15081679579785633615 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceLT___redArg___closed__2_value) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value: leanh::LeanArrayObject<5> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceLE___redArg___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [76, 69, 0],
    };
static mut l_Char_reduceLE___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceLE___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceLE___redArg___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [108, 101, 0],
    };
static mut l_Char_reduceLE___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceLE___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceLE___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceLE___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            8347582161988589016 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceLE___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceLE___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceLE___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            7316284823769321069 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceLE___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceLE___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value) as *mut leanh::LeanObject,13221861683099380057 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceLE___redArg___closed__2_value) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value: leanh::LeanArrayObject<5> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceGT___redArg___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [71, 84, 0],
    };
static mut l_Char_reduceGT___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceGT___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceGT___redArg___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [103, 116, 0],
    };
static mut l_Char_reduceGT___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceGT___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceGT___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceGT___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            2272833755566510320 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceGT___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceGT___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceGT___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            9426339939459091439 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceGT___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceGT___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 71, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value) as *mut leanh::LeanObject,12336814873061754153 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceGE___redArg___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [71, 69, 0],
    };
static mut l_Char_reduceGE___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceGE___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceGE___redArg___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [103, 101, 0],
    };
static mut l_Char_reduceGE___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceGE___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceGE___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceGE___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            1755019837031360842 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceGE___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceGE___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceGE___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            5555145617058846791 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceGE___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceGE___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 71, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value) as *mut leanh::LeanObject,16837157289316431972 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceEq___redArg___closed__0_value: leanh::LeanStringObject<3> =
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
static mut l_Char_reduceEq___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceEq___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceEq___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceEq___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceEq___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceEq___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject,3303585910804813030 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceEq___redArg___closed__1_value) as *mut leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value: leanh::LeanArrayObject<4> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceNe___redArg___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [78, 101, 0],
    };
static mut l_Char_reduceNe___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceNe___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceNe___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceNe___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            6695605208187598753 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceNe___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceNe___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 78, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject,7006235676040216717 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject,16612019923665488825 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value: leanh::LeanArrayObject<5> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceBEq___redArg___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [66, 69, 113, 0],
    };
static mut l_Char_reduceBEq___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBEq___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceBEq___redArg___closed__1_value: leanh::LeanStringObject<4> =
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
        m_data: [98, 101, 113, 0],
    };
static mut l_Char_reduceBEq___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBEq___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceBEq___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceBEq___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            16093780639914376387 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceBEq___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceBEq___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceBEq___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            9753356465987597394 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceBEq___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBEq___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value) as *mut leanh::LeanObject,3290093016162962346 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceBEq___redArg___closed__2_value) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value: leanh::LeanArrayObject<5> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceBNe___redArg___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [98, 110, 101, 0],
    };
static mut l_Char_reduceBNe___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBNe___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceBNe___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceBNe___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            943799886658452456 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceBNe___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceBNe___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 66, 78, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value) as *mut leanh::LeanObject,10534035068099563764 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceBNe___redArg___closed__1_value) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value: leanh::LeanArrayObject<5> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 115, 86, 97, 108, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value) as *mut leanh::LeanObject,15413451680662220155 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__4_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceOfNatAux___redArg___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 102, 78, 97, 116, 65, 117, 120, 0],
    };
static mut l_Char_reduceOfNatAux___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceOfNatAux___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_reduceOfNatAux___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            14164462494711235346 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceOfNatAux___redArg___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceOfNatAux___redArg___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceOfNatAux___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            13270590955479100020 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceOfNatAux___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceOfNatAux___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [114, 101, 100, 117, 99, 101, 79, 102, 78, 97, 116, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value) as *mut leanh::LeanObject,977086744675498421 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceOfNatAux___redArg___closed__1_value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value: leanh::LeanArrayObject<3> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_reduceDefault___redArg___closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [73, 110, 104, 97, 98, 105, 116, 101, 100, 0],
    };
static mut l_Char_reduceDefault___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceDefault___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_reduceDefault___redArg___closed__1_value: leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 102, 97, 117, 108, 116, 0],
    };
static mut l_Char_reduceDefault___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceDefault___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_reduceDefault___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceDefault___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            13340093926952294564 as *mut leanh::LeanObject,
        ],
    };
pub static l_Char_reduceDefault___redArg___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Char_reduceDefault___redArg___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Char_reduceDefault___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            609174137020324014 as *mut leanh::LeanObject,
        ],
    };
static mut l_Char_reduceDefault___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_reduceDefault___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Char_reduceDefault___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceDefault___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_reduceDefault___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceDefault___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_reduceDefault___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_reduceDefault___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 100, 117, 99, 101, 68, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value) as *mut leanh::LeanObject,12230170660042077464 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_reduceDefault___redArg___closed__2_value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value: leanh::LeanArrayObject<3> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__1_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [100, 105, 103, 105, 116, 67, 104, 97, 114, 0],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        6541421663447454700 as *mut leanh::LeanObject,
    ],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__4_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [100, 105, 103, 105, 116, 67, 104, 97, 114, 95, 110, 101, 0],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static l_Char_Nat_reduceDigitCharEq___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__5_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        13165569288841879117 as *mut leanh::LeanObject,
    ],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__7_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [101, 113, 95, 102, 97, 108, 115, 101, 0],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__8_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        1953906391527423986 as *mut leanh::LeanObject,
    ],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__10_value:
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
    m_data: [70, 97, 108, 115, 101, 0],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Char_Nat_reduceDigitCharEq___redArg___closed__11_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        907667957179513571 as *mut leanh::LeanObject,
    ],
};
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_Nat_reduceDigitCharEq___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 117, 99, 101, 68, 105, 103, 105, 116, 67, 104, 97, 114, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value) as *mut leanh::LeanObject,2094949447918665790 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value) as *mut leanh::LeanObject,9274808642807366986 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__2_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value: leanh::LeanArrayObject<5> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Char_Nat_reduceEqDigitChar___redArg___closed__0_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 121, 109, 109, 0],
};
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceEqDigitChar___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Char_Nat_reduceEqDigitChar___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Char_reduceNe___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        6695605208187598753 as *mut leanh::LeanObject,
    ],
};
pub static l_Char_Nat_reduceEqDigitChar___redArg___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Char_Nat_reduceEqDigitChar___redArg___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Char_Nat_reduceEqDigitChar___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        6773482220982667626 as *mut leanh::LeanObject,
    ],
};
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_Nat_reduceEqDigitChar___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_Nat_reduceEqDigitChar___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 117, 99, 101, 69, 113, 68, 105, 103, 105, 116, 67, 104, 97, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_reduceToLower___redArg___closed__0_value) as *mut leanh::LeanObject,14164462494711235346 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Char_Nat_reduceDigitCharEq___redArg___closed__0_value) as *mut leanh::LeanObject,2094949447918665790 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value) as *mut leanh::LeanObject,12972022006160371183 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value: leanh::LeanArrayObject<5> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Char_fromExpr_x3f___redArg(
    mut v_e_3587_: *mut leanh::LeanObject,
    mut v_a_3588_: *mut leanh::LeanObject,
    mut v_a_3589_: *mut leanh::LeanObject,
    mut v_a_3590_: *mut leanh::LeanObject,
    mut v_a_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3593_ =
        l_Lean_Meta_getCharValue_x3f(v_e_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
    return v___x_3593_;
}
pub unsafe fn l_Char_fromExpr_x3f___redArg___boxed(
    mut v_e_3594_: *mut leanh::LeanObject,
    mut v_a_3595_: *mut leanh::LeanObject,
    mut v_a_3596_: *mut leanh::LeanObject,
    mut v_a_3597_: *mut leanh::LeanObject,
    mut v_a_3598_: *mut leanh::LeanObject,
    mut v_a_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ =
        l_Char_fromExpr_x3f___redArg(v_e_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_);
    leanh::lean_dec(v_a_3598_);
    leanh::lean_dec_ref(v_a_3597_);
    leanh::lean_dec(v_a_3596_);
    leanh::lean_dec_ref(v_a_3595_);
    return v_res_3600_;
}
pub unsafe fn l_Char_fromExpr_x3f(
    mut v_e_3601_: *mut leanh::LeanObject,
    mut v_a_3602_: *mut leanh::LeanObject,
    mut v_a_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
    mut v_a_3605_: *mut leanh::LeanObject,
    mut v_a_3606_: *mut leanh::LeanObject,
    mut v_a_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3610_ =
        l_Lean_Meta_getCharValue_x3f(v_e_3601_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
    return v___x_3610_;
}
pub unsafe fn l_Char_fromExpr_x3f___boxed(
    mut v_e_3611_: *mut leanh::LeanObject,
    mut v_a_3612_: *mut leanh::LeanObject,
    mut v_a_3613_: *mut leanh::LeanObject,
    mut v_a_3614_: *mut leanh::LeanObject,
    mut v_a_3615_: *mut leanh::LeanObject,
    mut v_a_3616_: *mut leanh::LeanObject,
    mut v_a_3617_: *mut leanh::LeanObject,
    mut v_a_3618_: *mut leanh::LeanObject,
    mut v_a_3619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3620_ = l_Char_fromExpr_x3f(
        v_e_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_,
    );
    leanh::lean_dec(v_a_3618_);
    leanh::lean_dec_ref(v_a_3617_);
    leanh::lean_dec(v_a_3616_);
    leanh::lean_dec_ref(v_a_3615_);
    leanh::lean_dec(v_a_3614_);
    leanh::lean_dec_ref(v_a_3613_);
    leanh::lean_dec(v_a_3612_);
    return v_res_3620_;
}
pub unsafe fn l_Char_reduceUnary___redArg(
    mut v_inst_3623_: *mut leanh::LeanObject,
    mut v_declName_3624_: *mut leanh::LeanObject,
    mut v_op_3625_: *mut leanh::LeanObject,
    mut v_arity_3626_: *mut leanh::LeanObject,
    mut v_e_3627_: *mut leanh::LeanObject,
    mut v_a_3628_: *mut leanh::LeanObject,
    mut v_a_3629_: *mut leanh::LeanObject,
    mut v_a_3630_: *mut leanh::LeanObject,
    mut v_a_3631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3633_: u8 = 0;
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v_val_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3645_: u8 = 0;
    let mut v_toExpr_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3655_: u8 = 0;
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3660_: u8 = 0;
    let mut v_a_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3633_ = l_Lean_Expr_isAppOfArity(v_e_3627_, v_declName_3624_, v_arity_3626_);
                if v___x_3633_ == 0 {
                    leanh::lean_dec(v_op_3625_);
                    leanh::lean_dec_ref(v_inst_3623_);
                    v___x_3634_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_3635_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3635_, 0, v___x_3634_);
                    return v___x_3635_;
                } else {
                    v___x_3636_ = l_Lean_Expr_appArg_x21(v_e_3627_);
                    v___x_3637_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_3636_,
                        v_a_3628_,
                        v_a_3629_,
                        v_a_3630_,
                        v_a_3631_,
                    );
                    if leanh::lean_obj_tag(v___x_3637_) == 0 {
                        v_a_3638_ = leanh::lean_ctor_get(v___x_3637_, 0);
                        v_isSharedCheck_3660_ =
                            (!leanh::lean_is_exclusive(v___x_3637_)) as u8;
                        if v_isSharedCheck_3660_ == 0 {
                            v___x_3640_ = v___x_3637_;
                            v_isShared_3641_ = v_isSharedCheck_3660_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3638_);
                            leanh::lean_dec(v___x_3637_);
                            v___x_3640_ = leanh::lean_box(0);
                            v_isShared_3641_ = v_isSharedCheck_3660_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_op_3625_);
                        leanh::lean_dec_ref(v_inst_3623_);
                        v_a_3661_ = leanh::lean_ctor_get(v___x_3637_, 0);
                        v_isSharedCheck_3668_ =
                            (!leanh::lean_is_exclusive(v___x_3637_)) as u8;
                        if v_isSharedCheck_3668_ == 0 {
                            v___x_3663_ = v___x_3637_;
                            v_isShared_3664_ = v_isSharedCheck_3668_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3661_);
                            leanh::lean_dec(v___x_3637_);
                            v___x_3663_ = leanh::lean_box(0);
                            v_isShared_3664_ = v_isSharedCheck_3668_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3638_) == 1 {
                    v_val_3642_ = leanh::lean_ctor_get(v_a_3638_, 0);
                    v_isSharedCheck_3655_ = (!leanh::lean_is_exclusive(v_a_3638_)) as u8;
                    if v_isSharedCheck_3655_ == 0 {
                        v___x_3644_ = v_a_3638_;
                        v_isShared_3645_ = v_isSharedCheck_3655_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3642_);
                        leanh::lean_dec(v_a_3638_);
                        v___x_3644_ = leanh::lean_box(0);
                        v_isShared_3645_ = v_isSharedCheck_3655_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3638_);
                    leanh::lean_dec(v_op_3625_);
                    leanh::lean_dec_ref(v_inst_3623_);
                    v___x_3656_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_3641_ == 0 {
                        leanh::lean_ctor_set(v___x_3640_, 0, v___x_3656_);
                        v___x_3658_ = v___x_3640_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3659_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3656_);
                        v___x_3658_ = v_reuseFailAlloc_3659_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_toExpr_3646_ = leanh::lean_ctor_get(v_inst_3623_, 0);
                leanh::lean_inc_ref(v_toExpr_3646_);
                leanh::lean_dec_ref(v_inst_3623_);
                v___x_3647_ = leanh::lean_apply_1(v_op_3625_, v_val_3642_);
                v___x_3648_ = leanh::lean_apply_1(v_toExpr_3646_, v___x_3647_);
                if v_isShared_3645_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3644_, 0);
                    leanh::lean_ctor_set(v___x_3644_, 0, v___x_3648_);
                    v___x_3650_ = v___x_3644_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3654_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3648_);
                    v___x_3650_ = v_reuseFailAlloc_3654_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3641_ == 0 {
                    leanh::lean_ctor_set(v___x_3640_, 0, v___x_3650_);
                    v___x_3652_ = v___x_3640_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3650_);
                    v___x_3652_ = v_reuseFailAlloc_3653_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3652_;
            }
            5 => {
                return v___x_3658_;
            }
            6 => {
                if v_isShared_3664_ == 0 {
                    v___x_3666_ = v___x_3663_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3667_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
                    v___x_3666_ = v_reuseFailAlloc_3667_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceUnary___redArg___boxed(
    mut v_inst_3669_: *mut leanh::LeanObject,
    mut v_declName_3670_: *mut leanh::LeanObject,
    mut v_op_3671_: *mut leanh::LeanObject,
    mut v_arity_3672_: *mut leanh::LeanObject,
    mut v_e_3673_: *mut leanh::LeanObject,
    mut v_a_3674_: *mut leanh::LeanObject,
    mut v_a_3675_: *mut leanh::LeanObject,
    mut v_a_3676_: *mut leanh::LeanObject,
    mut v_a_3677_: *mut leanh::LeanObject,
    mut v_a_3678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3679_ = l_Char_reduceUnary___redArg(
        v_inst_3669_,
        v_declName_3670_,
        v_op_3671_,
        v_arity_3672_,
        v_e_3673_,
        v_a_3674_,
        v_a_3675_,
        v_a_3676_,
        v_a_3677_,
    );
    leanh::lean_dec(v_a_3677_);
    leanh::lean_dec_ref(v_a_3676_);
    leanh::lean_dec(v_a_3675_);
    leanh::lean_dec_ref(v_a_3674_);
    leanh::lean_dec_ref(v_e_3673_);
    leanh::lean_dec(v_declName_3670_);
    return v_res_3679_;
}
pub unsafe fn l_Char_reduceUnary(
    mut v_00_u03b1_3680_: *mut leanh::LeanObject,
    mut v_inst_3681_: *mut leanh::LeanObject,
    mut v_declName_3682_: *mut leanh::LeanObject,
    mut v_op_3683_: *mut leanh::LeanObject,
    mut v_arity_3684_: *mut leanh::LeanObject,
    mut v_e_3685_: *mut leanh::LeanObject,
    mut v_a_3686_: *mut leanh::LeanObject,
    mut v_a_3687_: *mut leanh::LeanObject,
    mut v_a_3688_: *mut leanh::LeanObject,
    mut v_a_3689_: *mut leanh::LeanObject,
    mut v_a_3690_: *mut leanh::LeanObject,
    mut v_a_3691_: *mut leanh::LeanObject,
    mut v_a_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3694_: u8 = 0;
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v_val_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v_toExpr_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3721_: u8 = 0;
    let mut v_a_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3694_ = l_Lean_Expr_isAppOfArity(v_e_3685_, v_declName_3682_, v_arity_3684_);
                if v___x_3694_ == 0 {
                    leanh::lean_dec(v_op_3683_);
                    leanh::lean_dec_ref(v_inst_3681_);
                    v___x_3695_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_3696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3696_, 0, v___x_3695_);
                    return v___x_3696_;
                } else {
                    v___x_3697_ = l_Lean_Expr_appArg_x21(v_e_3685_);
                    v___x_3698_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_3697_,
                        v_a_3689_,
                        v_a_3690_,
                        v_a_3691_,
                        v_a_3692_,
                    );
                    if leanh::lean_obj_tag(v___x_3698_) == 0 {
                        v_a_3699_ = leanh::lean_ctor_get(v___x_3698_, 0);
                        v_isSharedCheck_3721_ =
                            (!leanh::lean_is_exclusive(v___x_3698_)) as u8;
                        if v_isSharedCheck_3721_ == 0 {
                            v___x_3701_ = v___x_3698_;
                            v_isShared_3702_ = v_isSharedCheck_3721_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3699_);
                            leanh::lean_dec(v___x_3698_);
                            v___x_3701_ = leanh::lean_box(0);
                            v_isShared_3702_ = v_isSharedCheck_3721_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_op_3683_);
                        leanh::lean_dec_ref(v_inst_3681_);
                        v_a_3722_ = leanh::lean_ctor_get(v___x_3698_, 0);
                        v_isSharedCheck_3729_ =
                            (!leanh::lean_is_exclusive(v___x_3698_)) as u8;
                        if v_isSharedCheck_3729_ == 0 {
                            v___x_3724_ = v___x_3698_;
                            v_isShared_3725_ = v_isSharedCheck_3729_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3722_);
                            leanh::lean_dec(v___x_3698_);
                            v___x_3724_ = leanh::lean_box(0);
                            v_isShared_3725_ = v_isSharedCheck_3729_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3699_) == 1 {
                    v_val_3703_ = leanh::lean_ctor_get(v_a_3699_, 0);
                    v_isSharedCheck_3716_ = (!leanh::lean_is_exclusive(v_a_3699_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v___x_3705_ = v_a_3699_;
                        v_isShared_3706_ = v_isSharedCheck_3716_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3703_);
                        leanh::lean_dec(v_a_3699_);
                        v___x_3705_ = leanh::lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3716_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3699_);
                    leanh::lean_dec(v_op_3683_);
                    leanh::lean_dec_ref(v_inst_3681_);
                    v___x_3717_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_3702_ == 0 {
                        leanh::lean_ctor_set(v___x_3701_, 0, v___x_3717_);
                        v___x_3719_ = v___x_3701_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3717_);
                        v___x_3719_ = v_reuseFailAlloc_3720_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_toExpr_3707_ = leanh::lean_ctor_get(v_inst_3681_, 0);
                leanh::lean_inc_ref(v_toExpr_3707_);
                leanh::lean_dec_ref(v_inst_3681_);
                v___x_3708_ = leanh::lean_apply_1(v_op_3683_, v_val_3703_);
                v___x_3709_ = leanh::lean_apply_1(v_toExpr_3707_, v___x_3708_);
                if v_isShared_3706_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3705_, 0);
                    leanh::lean_ctor_set(v___x_3705_, 0, v___x_3709_);
                    v___x_3711_ = v___x_3705_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3709_);
                    v___x_3711_ = v_reuseFailAlloc_3715_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3702_ == 0 {
                    leanh::lean_ctor_set(v___x_3701_, 0, v___x_3711_);
                    v___x_3713_ = v___x_3701_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3714_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3711_);
                    v___x_3713_ = v_reuseFailAlloc_3714_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3713_;
            }
            5 => {
                return v___x_3719_;
            }
            6 => {
                if v_isShared_3725_ == 0 {
                    v___x_3727_ = v___x_3724_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3728_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
                    v___x_3727_ = v_reuseFailAlloc_3728_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceUnary___boxed(
    mut v_00_u03b1_3730_: *mut leanh::LeanObject,
    mut v_inst_3731_: *mut leanh::LeanObject,
    mut v_declName_3732_: *mut leanh::LeanObject,
    mut v_op_3733_: *mut leanh::LeanObject,
    mut v_arity_3734_: *mut leanh::LeanObject,
    mut v_e_3735_: *mut leanh::LeanObject,
    mut v_a_3736_: *mut leanh::LeanObject,
    mut v_a_3737_: *mut leanh::LeanObject,
    mut v_a_3738_: *mut leanh::LeanObject,
    mut v_a_3739_: *mut leanh::LeanObject,
    mut v_a_3740_: *mut leanh::LeanObject,
    mut v_a_3741_: *mut leanh::LeanObject,
    mut v_a_3742_: *mut leanh::LeanObject,
    mut v_a_3743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3744_ = l_Char_reduceUnary(
        v_00_u03b1_3730_,
        v_inst_3731_,
        v_declName_3732_,
        v_op_3733_,
        v_arity_3734_,
        v_e_3735_,
        v_a_3736_,
        v_a_3737_,
        v_a_3738_,
        v_a_3739_,
        v_a_3740_,
        v_a_3741_,
        v_a_3742_,
    );
    leanh::lean_dec(v_a_3742_);
    leanh::lean_dec_ref(v_a_3741_);
    leanh::lean_dec(v_a_3740_);
    leanh::lean_dec_ref(v_a_3739_);
    leanh::lean_dec(v_a_3738_);
    leanh::lean_dec_ref(v_a_3737_);
    leanh::lean_dec(v_a_3736_);
    leanh::lean_dec_ref(v_e_3735_);
    leanh::lean_dec(v_declName_3732_);
    return v_res_3744_;
}
pub unsafe fn l_Char_reduceBinPred___redArg(
    mut v_declName_3747_: *mut leanh::LeanObject,
    mut v_arity_3748_: *mut leanh::LeanObject,
    mut v_op_3749_: *mut leanh::LeanObject,
    mut v_e_3750_: *mut leanh::LeanObject,
    mut v_a_3751_: *mut leanh::LeanObject,
    mut v_a_3752_: *mut leanh::LeanObject,
    mut v_a_3753_: *mut leanh::LeanObject,
    mut v_a_3754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v_val_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v_val_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v_a_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3794_: u8 = 0;
    let mut v_a_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3756_ = l_Lean_Expr_isAppOfArity(v_e_3750_, v_declName_3747_, v_arity_3748_);
                if v___x_3756_ == 0 {
                    leanh::lean_dec_ref(v_e_3750_);
                    leanh::lean_dec_ref(v_op_3749_);
                    v___x_3757_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_3758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3758_, 0, v___x_3757_);
                    return v___x_3758_;
                } else {
                    v___x_3759_ = l_Lean_Expr_appFn_x21(v_e_3750_);
                    v___x_3760_ = l_Lean_Expr_appArg_x21(v___x_3759_);
                    leanh::lean_dec_ref(v___x_3759_);
                    v___x_3761_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_3760_,
                        v_a_3751_,
                        v_a_3752_,
                        v_a_3753_,
                        v_a_3754_,
                    );
                    if leanh::lean_obj_tag(v___x_3761_) == 0 {
                        v_a_3762_ = leanh::lean_ctor_get(v___x_3761_, 0);
                        v_isSharedCheck_3794_ =
                            (!leanh::lean_is_exclusive(v___x_3761_)) as u8;
                        if v_isSharedCheck_3794_ == 0 {
                            v___x_3764_ = v___x_3761_;
                            v_isShared_3765_ = v_isSharedCheck_3794_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3762_);
                            leanh::lean_dec(v___x_3761_);
                            v___x_3764_ = leanh::lean_box(0);
                            v_isShared_3765_ = v_isSharedCheck_3794_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3750_);
                        leanh::lean_dec_ref(v_op_3749_);
                        v_a_3795_ = leanh::lean_ctor_get(v___x_3761_, 0);
                        v_isSharedCheck_3802_ =
                            (!leanh::lean_is_exclusive(v___x_3761_)) as u8;
                        if v_isSharedCheck_3802_ == 0 {
                            v___x_3797_ = v___x_3761_;
                            v_isShared_3798_ = v_isSharedCheck_3802_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3795_);
                            leanh::lean_dec(v___x_3761_);
                            v___x_3797_ = leanh::lean_box(0);
                            v_isShared_3798_ = v_isSharedCheck_3802_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3762_) == 1 {
                    leanh::lean_del_object(v___x_3764_);
                    v_val_3766_ = leanh::lean_ctor_get(v_a_3762_, 0);
                    leanh::lean_inc(v_val_3766_);
                    leanh::lean_dec_ref_known(v_a_3762_, 1);
                    v___x_3767_ = l_Lean_Expr_appArg_x21(v_e_3750_);
                    v___x_3768_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_3767_,
                        v_a_3751_,
                        v_a_3752_,
                        v_a_3753_,
                        v_a_3754_,
                    );
                    if leanh::lean_obj_tag(v___x_3768_) == 0 {
                        v_a_3769_ = leanh::lean_ctor_get(v___x_3768_, 0);
                        v_isSharedCheck_3781_ =
                            (!leanh::lean_is_exclusive(v___x_3768_)) as u8;
                        if v_isSharedCheck_3781_ == 0 {
                            v___x_3771_ = v___x_3768_;
                            v_isShared_3772_ = v_isSharedCheck_3781_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3769_);
                            leanh::lean_dec(v___x_3768_);
                            v___x_3771_ = leanh::lean_box(0);
                            v_isShared_3772_ = v_isSharedCheck_3781_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_3766_);
                        leanh::lean_dec_ref(v_e_3750_);
                        leanh::lean_dec_ref(v_op_3749_);
                        v_a_3782_ = leanh::lean_ctor_get(v___x_3768_, 0);
                        v_isSharedCheck_3789_ =
                            (!leanh::lean_is_exclusive(v___x_3768_)) as u8;
                        if v_isSharedCheck_3789_ == 0 {
                            v___x_3784_ = v___x_3768_;
                            v_isShared_3785_ = v_isSharedCheck_3789_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3782_);
                            leanh::lean_dec(v___x_3768_);
                            v___x_3784_ = leanh::lean_box(0);
                            v_isShared_3785_ = v_isSharedCheck_3789_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3762_);
                    leanh::lean_dec_ref(v_e_3750_);
                    leanh::lean_dec_ref(v_op_3749_);
                    v___x_3790_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_3765_ == 0 {
                        leanh::lean_ctor_set(v___x_3764_, 0, v___x_3790_);
                        v___x_3792_ = v___x_3764_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3790_);
                        v___x_3792_ = v_reuseFailAlloc_3793_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3769_) == 1 {
                    leanh::lean_del_object(v___x_3771_);
                    v_val_3773_ = leanh::lean_ctor_get(v_a_3769_, 0);
                    leanh::lean_inc(v_val_3773_);
                    leanh::lean_dec_ref_known(v_a_3769_, 1);
                    v___x_3774_ = leanh::lean_apply_2(v_op_3749_, v_val_3766_, v_val_3773_);
                    v___x_3775_ = (leanh::lean_unbox(v___x_3774_) as u8);
                    v___x_3776_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_3750_,
                        v___x_3775_,
                        v_a_3751_,
                        v_a_3752_,
                        v_a_3753_,
                        v_a_3754_,
                    );
                    return v___x_3776_;
                } else {
                    leanh::lean_dec(v_a_3769_);
                    leanh::lean_dec(v_val_3766_);
                    leanh::lean_dec_ref(v_e_3750_);
                    leanh::lean_dec_ref(v_op_3749_);
                    v___x_3777_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_3772_ == 0 {
                        leanh::lean_ctor_set(v___x_3771_, 0, v___x_3777_);
                        v___x_3779_ = v___x_3771_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3780_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3777_);
                        v___x_3779_ = v_reuseFailAlloc_3780_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3779_;
            }
            4 => {
                if v_isShared_3785_ == 0 {
                    v___x_3787_ = v___x_3784_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
                    v___x_3787_ = v_reuseFailAlloc_3788_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3787_;
            }
            6 => {
                return v___x_3792_;
            }
            7 => {
                if v_isShared_3798_ == 0 {
                    v___x_3800_ = v___x_3797_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3801_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
                    v___x_3800_ = v_reuseFailAlloc_3801_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceBinPred___redArg___boxed(
    mut v_declName_3803_: *mut leanh::LeanObject,
    mut v_arity_3804_: *mut leanh::LeanObject,
    mut v_op_3805_: *mut leanh::LeanObject,
    mut v_e_3806_: *mut leanh::LeanObject,
    mut v_a_3807_: *mut leanh::LeanObject,
    mut v_a_3808_: *mut leanh::LeanObject,
    mut v_a_3809_: *mut leanh::LeanObject,
    mut v_a_3810_: *mut leanh::LeanObject,
    mut v_a_3811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3812_ = l_Char_reduceBinPred___redArg(
        v_declName_3803_,
        v_arity_3804_,
        v_op_3805_,
        v_e_3806_,
        v_a_3807_,
        v_a_3808_,
        v_a_3809_,
        v_a_3810_,
    );
    leanh::lean_dec(v_a_3810_);
    leanh::lean_dec_ref(v_a_3809_);
    leanh::lean_dec(v_a_3808_);
    leanh::lean_dec_ref(v_a_3807_);
    leanh::lean_dec(v_declName_3803_);
    return v_res_3812_;
}
pub unsafe fn l_Char_reduceBinPred(
    mut v_declName_3813_: *mut leanh::LeanObject,
    mut v_arity_3814_: *mut leanh::LeanObject,
    mut v_op_3815_: *mut leanh::LeanObject,
    mut v_e_3816_: *mut leanh::LeanObject,
    mut v_a_3817_: *mut leanh::LeanObject,
    mut v_a_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
    mut v_a_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_a_3822_: *mut leanh::LeanObject,
    mut v_a_3823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3825_: u8 = 0;
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3834_: u8 = 0;
    let mut v_val_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3841_: u8 = 0;
    let mut v_val_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_a_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3854_: u8 = 0;
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3863_: u8 = 0;
    let mut v_a_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3825_ = l_Lean_Expr_isAppOfArity(v_e_3816_, v_declName_3813_, v_arity_3814_);
                if v___x_3825_ == 0 {
                    leanh::lean_dec_ref(v_e_3816_);
                    leanh::lean_dec_ref(v_op_3815_);
                    v___x_3826_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_3827_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3827_, 0, v___x_3826_);
                    return v___x_3827_;
                } else {
                    v___x_3828_ = l_Lean_Expr_appFn_x21(v_e_3816_);
                    v___x_3829_ = l_Lean_Expr_appArg_x21(v___x_3828_);
                    leanh::lean_dec_ref(v___x_3828_);
                    v___x_3830_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_3829_,
                        v_a_3820_,
                        v_a_3821_,
                        v_a_3822_,
                        v_a_3823_,
                    );
                    if leanh::lean_obj_tag(v___x_3830_) == 0 {
                        v_a_3831_ = leanh::lean_ctor_get(v___x_3830_, 0);
                        v_isSharedCheck_3863_ =
                            (!leanh::lean_is_exclusive(v___x_3830_)) as u8;
                        if v_isSharedCheck_3863_ == 0 {
                            v___x_3833_ = v___x_3830_;
                            v_isShared_3834_ = v_isSharedCheck_3863_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3831_);
                            leanh::lean_dec(v___x_3830_);
                            v___x_3833_ = leanh::lean_box(0);
                            v_isShared_3834_ = v_isSharedCheck_3863_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3816_);
                        leanh::lean_dec_ref(v_op_3815_);
                        v_a_3864_ = leanh::lean_ctor_get(v___x_3830_, 0);
                        v_isSharedCheck_3871_ =
                            (!leanh::lean_is_exclusive(v___x_3830_)) as u8;
                        if v_isSharedCheck_3871_ == 0 {
                            v___x_3866_ = v___x_3830_;
                            v_isShared_3867_ = v_isSharedCheck_3871_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3864_);
                            leanh::lean_dec(v___x_3830_);
                            v___x_3866_ = leanh::lean_box(0);
                            v_isShared_3867_ = v_isSharedCheck_3871_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3831_) == 1 {
                    leanh::lean_del_object(v___x_3833_);
                    v_val_3835_ = leanh::lean_ctor_get(v_a_3831_, 0);
                    leanh::lean_inc(v_val_3835_);
                    leanh::lean_dec_ref_known(v_a_3831_, 1);
                    v___x_3836_ = l_Lean_Expr_appArg_x21(v_e_3816_);
                    v___x_3837_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_3836_,
                        v_a_3820_,
                        v_a_3821_,
                        v_a_3822_,
                        v_a_3823_,
                    );
                    if leanh::lean_obj_tag(v___x_3837_) == 0 {
                        v_a_3838_ = leanh::lean_ctor_get(v___x_3837_, 0);
                        v_isSharedCheck_3850_ =
                            (!leanh::lean_is_exclusive(v___x_3837_)) as u8;
                        if v_isSharedCheck_3850_ == 0 {
                            v___x_3840_ = v___x_3837_;
                            v_isShared_3841_ = v_isSharedCheck_3850_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3838_);
                            leanh::lean_dec(v___x_3837_);
                            v___x_3840_ = leanh::lean_box(0);
                            v_isShared_3841_ = v_isSharedCheck_3850_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_3835_);
                        leanh::lean_dec_ref(v_e_3816_);
                        leanh::lean_dec_ref(v_op_3815_);
                        v_a_3851_ = leanh::lean_ctor_get(v___x_3837_, 0);
                        v_isSharedCheck_3858_ =
                            (!leanh::lean_is_exclusive(v___x_3837_)) as u8;
                        if v_isSharedCheck_3858_ == 0 {
                            v___x_3853_ = v___x_3837_;
                            v_isShared_3854_ = v_isSharedCheck_3858_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3851_);
                            leanh::lean_dec(v___x_3837_);
                            v___x_3853_ = leanh::lean_box(0);
                            v_isShared_3854_ = v_isSharedCheck_3858_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3831_);
                    leanh::lean_dec_ref(v_e_3816_);
                    leanh::lean_dec_ref(v_op_3815_);
                    v___x_3859_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_3834_ == 0 {
                        leanh::lean_ctor_set(v___x_3833_, 0, v___x_3859_);
                        v___x_3861_ = v___x_3833_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
                        v___x_3861_ = v_reuseFailAlloc_3862_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3838_) == 1 {
                    leanh::lean_del_object(v___x_3840_);
                    v_val_3842_ = leanh::lean_ctor_get(v_a_3838_, 0);
                    leanh::lean_inc(v_val_3842_);
                    leanh::lean_dec_ref_known(v_a_3838_, 1);
                    v___x_3843_ = leanh::lean_apply_2(v_op_3815_, v_val_3835_, v_val_3842_);
                    v___x_3844_ = (leanh::lean_unbox(v___x_3843_) as u8);
                    v___x_3845_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_3816_,
                        v___x_3844_,
                        v_a_3820_,
                        v_a_3821_,
                        v_a_3822_,
                        v_a_3823_,
                    );
                    return v___x_3845_;
                } else {
                    leanh::lean_dec(v_a_3838_);
                    leanh::lean_dec(v_val_3835_);
                    leanh::lean_dec_ref(v_e_3816_);
                    leanh::lean_dec_ref(v_op_3815_);
                    v___x_3846_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_3841_ == 0 {
                        leanh::lean_ctor_set(v___x_3840_, 0, v___x_3846_);
                        v___x_3848_ = v___x_3840_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3849_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
                        v___x_3848_ = v_reuseFailAlloc_3849_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3848_;
            }
            4 => {
                if v_isShared_3854_ == 0 {
                    v___x_3856_ = v___x_3853_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3857_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
                    v___x_3856_ = v_reuseFailAlloc_3857_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3856_;
            }
            6 => {
                return v___x_3861_;
            }
            7 => {
                if v_isShared_3867_ == 0 {
                    v___x_3869_ = v___x_3866_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3870_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
                    v___x_3869_ = v_reuseFailAlloc_3870_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceBinPred___boxed(
    mut v_declName_3872_: *mut leanh::LeanObject,
    mut v_arity_3873_: *mut leanh::LeanObject,
    mut v_op_3874_: *mut leanh::LeanObject,
    mut v_e_3875_: *mut leanh::LeanObject,
    mut v_a_3876_: *mut leanh::LeanObject,
    mut v_a_3877_: *mut leanh::LeanObject,
    mut v_a_3878_: *mut leanh::LeanObject,
    mut v_a_3879_: *mut leanh::LeanObject,
    mut v_a_3880_: *mut leanh::LeanObject,
    mut v_a_3881_: *mut leanh::LeanObject,
    mut v_a_3882_: *mut leanh::LeanObject,
    mut v_a_3883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3884_ = l_Char_reduceBinPred(
        v_declName_3872_,
        v_arity_3873_,
        v_op_3874_,
        v_e_3875_,
        v_a_3876_,
        v_a_3877_,
        v_a_3878_,
        v_a_3879_,
        v_a_3880_,
        v_a_3881_,
        v_a_3882_,
    );
    leanh::lean_dec(v_a_3882_);
    leanh::lean_dec_ref(v_a_3881_);
    leanh::lean_dec(v_a_3880_);
    leanh::lean_dec_ref(v_a_3879_);
    leanh::lean_dec(v_a_3878_);
    leanh::lean_dec_ref(v_a_3877_);
    leanh::lean_dec(v_a_3876_);
    leanh::lean_dec(v_declName_3872_);
    return v_res_3884_;
}
pub unsafe fn _init_l_Char_reduceBoolPred___redArg___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = leanh::lean_box(0);
    v___x_3891_ = l_Char_reduceBoolPred___redArg___closed__2;
    v___x_3892_ = l_Lean_mkConst(v___x_3891_, v___x_3890_);
    return v___x_3892_;
}
pub unsafe fn _init_l_Char_reduceBoolPred___redArg___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3897_ = leanh::lean_box(0);
    v___x_3898_ = l_Char_reduceBoolPred___redArg___closed__5;
    v___x_3899_ = l_Lean_mkConst(v___x_3898_, v___x_3897_);
    return v___x_3899_;
}
pub unsafe fn l_Char_reduceBoolPred___redArg(
    mut v_declName_3900_: *mut leanh::LeanObject,
    mut v_arity_3901_: *mut leanh::LeanObject,
    mut v_op_3902_: *mut leanh::LeanObject,
    mut v_e_3903_: *mut leanh::LeanObject,
    mut v_a_3904_: *mut leanh::LeanObject,
    mut v_a_3905_: *mut leanh::LeanObject,
    mut v_a_3906_: *mut leanh::LeanObject,
    mut v_a_3907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3909_: u8 = 0;
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v_val_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___y_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_a_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3950_: u8 = 0;
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v_isSharedCheck_3955_: u8 = 0;
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut v_a_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3909_ = l_Lean_Expr_isAppOfArity(v_e_3903_, v_declName_3900_, v_arity_3901_);
                if v___x_3909_ == 0 {
                    leanh::lean_dec_ref(v_op_3902_);
                    v___x_3910_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_3911_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3911_, 0, v___x_3910_);
                    return v___x_3911_;
                } else {
                    v___x_3912_ = l_Lean_Expr_appFn_x21(v_e_3903_);
                    v___x_3913_ = l_Lean_Expr_appArg_x21(v___x_3912_);
                    leanh::lean_dec_ref(v___x_3912_);
                    v___x_3914_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_3913_,
                        v_a_3904_,
                        v_a_3905_,
                        v_a_3906_,
                        v_a_3907_,
                    );
                    if leanh::lean_obj_tag(v___x_3914_) == 0 {
                        v_a_3915_ = leanh::lean_ctor_get(v___x_3914_, 0);
                        v_isSharedCheck_3960_ =
                            (!leanh::lean_is_exclusive(v___x_3914_)) as u8;
                        if v_isSharedCheck_3960_ == 0 {
                            v___x_3917_ = v___x_3914_;
                            v_isShared_3918_ = v_isSharedCheck_3960_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3915_);
                            leanh::lean_dec(v___x_3914_);
                            v___x_3917_ = leanh::lean_box(0);
                            v_isShared_3918_ = v_isSharedCheck_3960_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_op_3902_);
                        v_a_3961_ = leanh::lean_ctor_get(v___x_3914_, 0);
                        v_isSharedCheck_3968_ =
                            (!leanh::lean_is_exclusive(v___x_3914_)) as u8;
                        if v_isSharedCheck_3968_ == 0 {
                            v___x_3963_ = v___x_3914_;
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3961_);
                            leanh::lean_dec(v___x_3914_);
                            v___x_3963_ = leanh::lean_box(0);
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3915_) == 1 {
                    v_val_3919_ = leanh::lean_ctor_get(v_a_3915_, 0);
                    v_isSharedCheck_3955_ = (!leanh::lean_is_exclusive(v_a_3915_)) as u8;
                    if v_isSharedCheck_3955_ == 0 {
                        v___x_3921_ = v_a_3915_;
                        v_isShared_3922_ = v_isSharedCheck_3955_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3919_);
                        leanh::lean_dec(v_a_3915_);
                        v___x_3921_ = leanh::lean_box(0);
                        v_isShared_3922_ = v_isSharedCheck_3955_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3915_);
                    leanh::lean_dec_ref(v_op_3902_);
                    v___x_3956_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_3918_ == 0 {
                        leanh::lean_ctor_set(v___x_3917_, 0, v___x_3956_);
                        v___x_3958_ = v___x_3917_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
                        v___x_3958_ = v_reuseFailAlloc_3959_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3923_ = l_Lean_Expr_appArg_x21(v_e_3903_);
                v___x_3924_ = l_Lean_Meta_getCharValue_x3f(
                    v___x_3923_,
                    v_a_3904_,
                    v_a_3905_,
                    v_a_3906_,
                    v_a_3907_,
                );
                if leanh::lean_obj_tag(v___x_3924_) == 0 {
                    v_a_3925_ = leanh::lean_ctor_get(v___x_3924_, 0);
                    v_isSharedCheck_3946_ = (!leanh::lean_is_exclusive(v___x_3924_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3927_ = v___x_3924_;
                        v_isShared_3928_ = v_isSharedCheck_3946_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3925_);
                        leanh::lean_dec(v___x_3924_);
                        v___x_3927_ = leanh::lean_box(0);
                        v_isShared_3928_ = v_isSharedCheck_3946_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3921_);
                    leanh::lean_dec(v_val_3919_);
                    leanh::lean_del_object(v___x_3917_);
                    leanh::lean_dec_ref(v_op_3902_);
                    v_a_3947_ = leanh::lean_ctor_get(v___x_3924_, 0);
                    v_isSharedCheck_3954_ = (!leanh::lean_is_exclusive(v___x_3924_)) as u8;
                    if v_isSharedCheck_3954_ == 0 {
                        v___x_3949_ = v___x_3924_;
                        v_isShared_3950_ = v_isSharedCheck_3954_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3947_);
                        leanh::lean_dec(v___x_3924_);
                        v___x_3949_ = leanh::lean_box(0);
                        v_isShared_3950_ = v_isSharedCheck_3954_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3925_) == 1 {
                    leanh::lean_del_object(v___x_3917_);
                    v_val_3937_ = leanh::lean_ctor_get(v_a_3925_, 0);
                    leanh::lean_inc(v_val_3937_);
                    leanh::lean_dec_ref_known(v_a_3925_, 1);
                    v___x_3938_ = leanh::lean_apply_2(v_op_3902_, v_val_3919_, v_val_3937_);
                    v___x_3939_ = (leanh::lean_unbox(v___x_3938_) as u8);
                    if v___x_3939_ == 0 {
                        v___x_3940_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Char_reduceBoolPred___redArg___closed__3_once
                            ),
                            _init_l_Char_reduceBoolPred___redArg___closed__3,
                        );
                        v___y_3930_ = v___x_3940_;
                        state = 4;
                        continue;
                    } else {
                        v___x_3941_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Char_reduceBoolPred___redArg___closed__6_once
                            ),
                            _init_l_Char_reduceBoolPred___redArg___closed__6,
                        );
                        v___y_3930_ = v___x_3941_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3927_);
                    leanh::lean_dec(v_a_3925_);
                    leanh::lean_del_object(v___x_3921_);
                    leanh::lean_dec(v_val_3919_);
                    leanh::lean_dec_ref(v_op_3902_);
                    v___x_3942_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_3918_ == 0 {
                        leanh::lean_ctor_set(v___x_3917_, 0, v___x_3942_);
                        v___x_3944_ = v___x_3917_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
                        v___x_3944_ = v_reuseFailAlloc_3945_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v___y_3930_);
                if v_isShared_3922_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3921_, 0);
                    leanh::lean_ctor_set(v___x_3921_, 0, v___y_3930_);
                    v___x_3932_ = v___x_3921_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3936_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___y_3930_);
                    v___x_3932_ = v_reuseFailAlloc_3936_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3928_ == 0 {
                    leanh::lean_ctor_set(v___x_3927_, 0, v___x_3932_);
                    v___x_3934_ = v___x_3927_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
                    v___x_3934_ = v_reuseFailAlloc_3935_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3934_;
            }
            7 => {
                return v___x_3944_;
            }
            8 => {
                if v_isShared_3950_ == 0 {
                    v___x_3952_ = v___x_3949_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
                    v___x_3952_ = v_reuseFailAlloc_3953_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3952_;
            }
            10 => {
                return v___x_3958_;
            }
            11 => {
                if v_isShared_3964_ == 0 {
                    v___x_3966_ = v___x_3963_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
                    v___x_3966_ = v_reuseFailAlloc_3967_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceBoolPred___redArg___boxed(
    mut v_declName_3969_: *mut leanh::LeanObject,
    mut v_arity_3970_: *mut leanh::LeanObject,
    mut v_op_3971_: *mut leanh::LeanObject,
    mut v_e_3972_: *mut leanh::LeanObject,
    mut v_a_3973_: *mut leanh::LeanObject,
    mut v_a_3974_: *mut leanh::LeanObject,
    mut v_a_3975_: *mut leanh::LeanObject,
    mut v_a_3976_: *mut leanh::LeanObject,
    mut v_a_3977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3978_ = l_Char_reduceBoolPred___redArg(
        v_declName_3969_,
        v_arity_3970_,
        v_op_3971_,
        v_e_3972_,
        v_a_3973_,
        v_a_3974_,
        v_a_3975_,
        v_a_3976_,
    );
    leanh::lean_dec(v_a_3976_);
    leanh::lean_dec_ref(v_a_3975_);
    leanh::lean_dec(v_a_3974_);
    leanh::lean_dec_ref(v_a_3973_);
    leanh::lean_dec_ref(v_e_3972_);
    leanh::lean_dec(v_declName_3969_);
    return v_res_3978_;
}
pub unsafe fn l_Char_reduceBoolPred(
    mut v_declName_3979_: *mut leanh::LeanObject,
    mut v_arity_3980_: *mut leanh::LeanObject,
    mut v_op_3981_: *mut leanh::LeanObject,
    mut v_e_3982_: *mut leanh::LeanObject,
    mut v_a_3983_: *mut leanh::LeanObject,
    mut v_a_3984_: *mut leanh::LeanObject,
    mut v_a_3985_: *mut leanh::LeanObject,
    mut v_a_3986_: *mut leanh::LeanObject,
    mut v_a_3987_: *mut leanh::LeanObject,
    mut v_a_3988_: *mut leanh::LeanObject,
    mut v_a_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v_val_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4010_: u8 = 0;
    let mut v___y_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4028_: u8 = 0;
    let mut v_a_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4032_: u8 = 0;
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v_isSharedCheck_4037_: u8 = 0;
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4042_: u8 = 0;
    let mut v_a_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4050_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3991_ = l_Lean_Expr_isAppOfArity(v_e_3982_, v_declName_3979_, v_arity_3980_);
                if v___x_3991_ == 0 {
                    leanh::lean_dec_ref(v_op_3981_);
                    v___x_3992_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_3993_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3993_, 0, v___x_3992_);
                    return v___x_3993_;
                } else {
                    v___x_3994_ = l_Lean_Expr_appFn_x21(v_e_3982_);
                    v___x_3995_ = l_Lean_Expr_appArg_x21(v___x_3994_);
                    leanh::lean_dec_ref(v___x_3994_);
                    v___x_3996_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_3995_,
                        v_a_3986_,
                        v_a_3987_,
                        v_a_3988_,
                        v_a_3989_,
                    );
                    if leanh::lean_obj_tag(v___x_3996_) == 0 {
                        v_a_3997_ = leanh::lean_ctor_get(v___x_3996_, 0);
                        v_isSharedCheck_4042_ =
                            (!leanh::lean_is_exclusive(v___x_3996_)) as u8;
                        if v_isSharedCheck_4042_ == 0 {
                            v___x_3999_ = v___x_3996_;
                            v_isShared_4000_ = v_isSharedCheck_4042_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3997_);
                            leanh::lean_dec(v___x_3996_);
                            v___x_3999_ = leanh::lean_box(0);
                            v_isShared_4000_ = v_isSharedCheck_4042_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_op_3981_);
                        v_a_4043_ = leanh::lean_ctor_get(v___x_3996_, 0);
                        v_isSharedCheck_4050_ =
                            (!leanh::lean_is_exclusive(v___x_3996_)) as u8;
                        if v_isSharedCheck_4050_ == 0 {
                            v___x_4045_ = v___x_3996_;
                            v_isShared_4046_ = v_isSharedCheck_4050_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4043_);
                            leanh::lean_dec(v___x_3996_);
                            v___x_4045_ = leanh::lean_box(0);
                            v_isShared_4046_ = v_isSharedCheck_4050_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3997_) == 1 {
                    v_val_4001_ = leanh::lean_ctor_get(v_a_3997_, 0);
                    v_isSharedCheck_4037_ = (!leanh::lean_is_exclusive(v_a_3997_)) as u8;
                    if v_isSharedCheck_4037_ == 0 {
                        v___x_4003_ = v_a_3997_;
                        v_isShared_4004_ = v_isSharedCheck_4037_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4001_);
                        leanh::lean_dec(v_a_3997_);
                        v___x_4003_ = leanh::lean_box(0);
                        v_isShared_4004_ = v_isSharedCheck_4037_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3997_);
                    leanh::lean_dec_ref(v_op_3981_);
                    v___x_4038_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_4000_ == 0 {
                        leanh::lean_ctor_set(v___x_3999_, 0, v___x_4038_);
                        v___x_4040_ = v___x_3999_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
                        v___x_4040_ = v_reuseFailAlloc_4041_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4005_ = l_Lean_Expr_appArg_x21(v_e_3982_);
                v___x_4006_ = l_Lean_Meta_getCharValue_x3f(
                    v___x_4005_,
                    v_a_3986_,
                    v_a_3987_,
                    v_a_3988_,
                    v_a_3989_,
                );
                if leanh::lean_obj_tag(v___x_4006_) == 0 {
                    v_a_4007_ = leanh::lean_ctor_get(v___x_4006_, 0);
                    v_isSharedCheck_4028_ = (!leanh::lean_is_exclusive(v___x_4006_)) as u8;
                    if v_isSharedCheck_4028_ == 0 {
                        v___x_4009_ = v___x_4006_;
                        v_isShared_4010_ = v_isSharedCheck_4028_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4007_);
                        leanh::lean_dec(v___x_4006_);
                        v___x_4009_ = leanh::lean_box(0);
                        v_isShared_4010_ = v_isSharedCheck_4028_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4003_);
                    leanh::lean_dec(v_val_4001_);
                    leanh::lean_del_object(v___x_3999_);
                    leanh::lean_dec_ref(v_op_3981_);
                    v_a_4029_ = leanh::lean_ctor_get(v___x_4006_, 0);
                    v_isSharedCheck_4036_ = (!leanh::lean_is_exclusive(v___x_4006_)) as u8;
                    if v_isSharedCheck_4036_ == 0 {
                        v___x_4031_ = v___x_4006_;
                        v_isShared_4032_ = v_isSharedCheck_4036_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4029_);
                        leanh::lean_dec(v___x_4006_);
                        v___x_4031_ = leanh::lean_box(0);
                        v_isShared_4032_ = v_isSharedCheck_4036_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_4007_) == 1 {
                    leanh::lean_del_object(v___x_3999_);
                    v_val_4019_ = leanh::lean_ctor_get(v_a_4007_, 0);
                    leanh::lean_inc(v_val_4019_);
                    leanh::lean_dec_ref_known(v_a_4007_, 1);
                    v___x_4020_ = leanh::lean_apply_2(v_op_3981_, v_val_4001_, v_val_4019_);
                    v___x_4021_ = (leanh::lean_unbox(v___x_4020_) as u8);
                    if v___x_4021_ == 0 {
                        v___x_4022_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Char_reduceBoolPred___redArg___closed__3_once
                            ),
                            _init_l_Char_reduceBoolPred___redArg___closed__3,
                        );
                        v___y_4012_ = v___x_4022_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4023_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Char_reduceBoolPred___redArg___closed__6_once
                            ),
                            _init_l_Char_reduceBoolPred___redArg___closed__6,
                        );
                        v___y_4012_ = v___x_4023_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4009_);
                    leanh::lean_dec(v_a_4007_);
                    leanh::lean_del_object(v___x_4003_);
                    leanh::lean_dec(v_val_4001_);
                    leanh::lean_dec_ref(v_op_3981_);
                    v___x_4024_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_4000_ == 0 {
                        leanh::lean_ctor_set(v___x_3999_, 0, v___x_4024_);
                        v___x_4026_ = v___x_3999_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
                        v___x_4026_ = v_reuseFailAlloc_4027_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v___y_4012_);
                if v_isShared_4004_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4003_, 0);
                    leanh::lean_ctor_set(v___x_4003_, 0, v___y_4012_);
                    v___x_4014_ = v___x_4003_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___y_4012_);
                    v___x_4014_ = v_reuseFailAlloc_4018_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4010_ == 0 {
                    leanh::lean_ctor_set(v___x_4009_, 0, v___x_4014_);
                    v___x_4016_ = v___x_4009_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4017_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4014_);
                    v___x_4016_ = v_reuseFailAlloc_4017_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4016_;
            }
            7 => {
                return v___x_4026_;
            }
            8 => {
                if v_isShared_4032_ == 0 {
                    v___x_4034_ = v___x_4031_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
                    v___x_4034_ = v_reuseFailAlloc_4035_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4034_;
            }
            10 => {
                return v___x_4040_;
            }
            11 => {
                if v_isShared_4046_ == 0 {
                    v___x_4048_ = v___x_4045_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4049_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
                    v___x_4048_ = v_reuseFailAlloc_4049_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceBoolPred___boxed(
    mut v_declName_4051_: *mut leanh::LeanObject,
    mut v_arity_4052_: *mut leanh::LeanObject,
    mut v_op_4053_: *mut leanh::LeanObject,
    mut v_e_4054_: *mut leanh::LeanObject,
    mut v_a_4055_: *mut leanh::LeanObject,
    mut v_a_4056_: *mut leanh::LeanObject,
    mut v_a_4057_: *mut leanh::LeanObject,
    mut v_a_4058_: *mut leanh::LeanObject,
    mut v_a_4059_: *mut leanh::LeanObject,
    mut v_a_4060_: *mut leanh::LeanObject,
    mut v_a_4061_: *mut leanh::LeanObject,
    mut v_a_4062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4063_ = l_Char_reduceBoolPred(
        v_declName_4051_,
        v_arity_4052_,
        v_op_4053_,
        v_e_4054_,
        v_a_4055_,
        v_a_4056_,
        v_a_4057_,
        v_a_4058_,
        v_a_4059_,
        v_a_4060_,
        v_a_4061_,
    );
    leanh::lean_dec(v_a_4061_);
    leanh::lean_dec_ref(v_a_4060_);
    leanh::lean_dec(v_a_4059_);
    leanh::lean_dec_ref(v_a_4058_);
    leanh::lean_dec(v_a_4057_);
    leanh::lean_dec_ref(v_a_4056_);
    leanh::lean_dec(v_a_4055_);
    leanh::lean_dec_ref(v_e_4054_);
    leanh::lean_dec(v_declName_4051_);
    return v_res_4063_;
}
pub unsafe fn _init_l_Char_reduceToLower___redArg___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4073_ = leanh::lean_box(0);
    v___x_4074_ = l_Char_reduceToLower___redArg___closed__4;
    v___x_4075_ = l_Lean_mkConst(v___x_4074_, v___x_4073_);
    return v___x_4075_;
}
pub unsafe fn l_Char_reduceToLower___redArg(
    mut v_e_4076_: *mut leanh::LeanObject,
    mut v_a_4077_: *mut leanh::LeanObject,
    mut v_a_4078_: *mut leanh::LeanObject,
    mut v_a_4079_: *mut leanh::LeanObject,
    mut v_a_4080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___y_4094_: u32 = 0;
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u32 = 0;
    let mut v___x_4105_: u32 = 0;
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: u32 = 0;
    let mut v___x_4108_: u32 = 0;
    let mut v___x_4109_: u32 = 0;
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: u32 = 0;
    let mut v___x_4112_: u32 = 0;
    let mut v___x_4113_: u32 = 0;
    let mut v___x_4114_: u32 = 0;
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_a_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4082_ = l_Char_reduceToLower___redArg___closed__2;
                v___x_4083_ = leanh::lean_unsigned_to_nat(1);
                v___x_4084_ = l_Lean_Expr_isAppOfArity(v_e_4076_, v___x_4082_, v___x_4083_);
                if v___x_4084_ == 0 {
                    v___x_4085_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4086_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4086_, 0, v___x_4085_);
                    return v___x_4086_;
                } else {
                    v___x_4087_ = l_Lean_Expr_appArg_x21(v_e_4076_);
                    v___x_4088_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_4087_,
                        v_a_4077_,
                        v_a_4078_,
                        v_a_4079_,
                        v_a_4080_,
                    );
                    if leanh::lean_obj_tag(v___x_4088_) == 0 {
                        v_a_4089_ = leanh::lean_ctor_get(v___x_4088_, 0);
                        v_isSharedCheck_4117_ =
                            (!leanh::lean_is_exclusive(v___x_4088_)) as u8;
                        if v_isSharedCheck_4117_ == 0 {
                            v___x_4091_ = v___x_4088_;
                            v_isShared_4092_ = v_isSharedCheck_4117_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4089_);
                            leanh::lean_dec(v___x_4088_);
                            v___x_4091_ = leanh::lean_box(0);
                            v_isShared_4092_ = v_isSharedCheck_4117_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4118_ = leanh::lean_ctor_get(v___x_4088_, 0);
                        v_isSharedCheck_4125_ =
                            (!leanh::lean_is_exclusive(v___x_4088_)) as u8;
                        if v_isSharedCheck_4125_ == 0 {
                            v___x_4120_ = v___x_4088_;
                            v_isShared_4121_ = v_isSharedCheck_4125_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4118_);
                            leanh::lean_dec(v___x_4088_);
                            v___x_4120_ = leanh::lean_box(0);
                            v_isShared_4121_ = v_isSharedCheck_4125_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4089_) == 1 {
                    v_val_4103_ = leanh::lean_ctor_get(v_a_4089_, 0);
                    leanh::lean_inc(v_val_4103_);
                    leanh::lean_dec_ref_known(v_a_4089_, 1);
                    v___x_4104_ = 65;
                    v___x_4105_ = leanh::lean_unbox_uint32(v_val_4103_);
                    v___x_4106_ = lean_uint32_dec_le(v___x_4104_, v___x_4105_);
                    if v___x_4106_ == 0 {
                        v___x_4107_ = leanh::lean_unbox_uint32(v_val_4103_);
                        leanh::lean_dec(v_val_4103_);
                        v___y_4094_ = v___x_4107_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4108_ = 90;
                        v___x_4109_ = leanh::lean_unbox_uint32(v_val_4103_);
                        v___x_4110_ = lean_uint32_dec_le(v___x_4109_, v___x_4108_);
                        if v___x_4110_ == 0 {
                            v___x_4111_ = leanh::lean_unbox_uint32(v_val_4103_);
                            leanh::lean_dec(v_val_4103_);
                            v___y_4094_ = v___x_4111_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4112_ = 32;
                            v___x_4113_ = leanh::lean_unbox_uint32(v_val_4103_);
                            leanh::lean_dec(v_val_4103_);
                            v___x_4114_ = lean_uint32_add(v___x_4113_, v___x_4112_);
                            v___y_4094_ = v___x_4114_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4091_);
                    leanh::lean_dec(v_a_4089_);
                    v___x_4115_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4116_, 0, v___x_4115_);
                    return v___x_4116_;
                }
            }
            2 => {
                v___x_4095_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceToLower___redArg___closed__5),
                    core::ptr::addr_of_mut!(l_Char_reduceToLower___redArg___closed__5_once),
                    _init_l_Char_reduceToLower___redArg___closed__5,
                );
                v___x_4096_ = lean_uint32_to_nat(v___y_4094_);
                v___x_4097_ = l_Lean_mkRawNatLit(v___x_4096_);
                v___x_4098_ = l_Lean_Expr_app___override(v___x_4095_, v___x_4097_);
                v___x_4099_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4099_, 0, v___x_4098_);
                if v_isShared_4092_ == 0 {
                    leanh::lean_ctor_set(v___x_4091_, 0, v___x_4099_);
                    v___x_4101_ = v___x_4091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4102_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
                    v___x_4101_ = v_reuseFailAlloc_4102_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4101_;
            }
            4 => {
                if v_isShared_4121_ == 0 {
                    v___x_4123_ = v___x_4120_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
                    v___x_4123_ = v_reuseFailAlloc_4124_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceToLower___redArg___boxed(
    mut v_e_4126_: *mut leanh::LeanObject,
    mut v_a_4127_: *mut leanh::LeanObject,
    mut v_a_4128_: *mut leanh::LeanObject,
    mut v_a_4129_: *mut leanh::LeanObject,
    mut v_a_4130_: *mut leanh::LeanObject,
    mut v_a_4131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4132_ =
        l_Char_reduceToLower___redArg(v_e_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
    leanh::lean_dec(v_a_4130_);
    leanh::lean_dec_ref(v_a_4129_);
    leanh::lean_dec(v_a_4128_);
    leanh::lean_dec_ref(v_a_4127_);
    leanh::lean_dec_ref(v_e_4126_);
    return v_res_4132_;
}
pub unsafe fn l_Char_reduceToLower(
    mut v_e_4133_: *mut leanh::LeanObject,
    mut v_a_4134_: *mut leanh::LeanObject,
    mut v_a_4135_: *mut leanh::LeanObject,
    mut v_a_4136_: *mut leanh::LeanObject,
    mut v_a_4137_: *mut leanh::LeanObject,
    mut v_a_4138_: *mut leanh::LeanObject,
    mut v_a_4139_: *mut leanh::LeanObject,
    mut v_a_4140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ =
        l_Char_reduceToLower___redArg(v_e_4133_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
    return v___x_4142_;
}
pub unsafe fn l_Char_reduceToLower___boxed(
    mut v_e_4143_: *mut leanh::LeanObject,
    mut v_a_4144_: *mut leanh::LeanObject,
    mut v_a_4145_: *mut leanh::LeanObject,
    mut v_a_4146_: *mut leanh::LeanObject,
    mut v_a_4147_: *mut leanh::LeanObject,
    mut v_a_4148_: *mut leanh::LeanObject,
    mut v_a_4149_: *mut leanh::LeanObject,
    mut v_a_4150_: *mut leanh::LeanObject,
    mut v_a_4151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4152_ = l_Char_reduceToLower(
        v_e_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_,
    );
    leanh::lean_dec(v_a_4150_);
    leanh::lean_dec_ref(v_a_4149_);
    leanh::lean_dec(v_a_4148_);
    leanh::lean_dec_ref(v_a_4147_);
    leanh::lean_dec(v_a_4146_);
    leanh::lean_dec_ref(v_a_4145_);
    leanh::lean_dec(v_a_4144_);
    leanh::lean_dec_ref(v_e_4143_);
    return v_res_4152_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_;
    v___x_4168_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_;
    v___x_4169_ = leanh::lean_alloc_closure(
        l_Char_reduceToLower___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4170_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4167_, v___x_4168_, v___x_4169_);
    return v___x_4170_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13____boxed(
    mut v_a_4171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4172_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_();
    return v_res_4172_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4173_ = leanh::lean_alloc_closure(
        l_Char_reduceToLower___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4174_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4174_, 0, v___x_4173_);
    return v___x_4174_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_;
    v___x_4177_ = 1;
    v___x_4178_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_);
    v___x_4179_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4176_, v___x_4177_, v___x_4178_);
    return v___x_4179_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15____boxed(
    mut v_a_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_();
    return v_res_4181_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: u8 = 0;
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4183_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_;
    v___x_4184_ = 1;
    v___x_4185_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_);
    v___x_4186_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4183_, v___x_4184_, v___x_4185_);
    return v___x_4186_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17____boxed(
    mut v_a_4187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4188_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17_();
    return v_res_4188_;
}
pub unsafe fn l_Char_reduceToUpper___redArg(
    mut v_e_4193_: *mut leanh::LeanObject,
    mut v_a_4194_: *mut leanh::LeanObject,
    mut v_a_4195_: *mut leanh::LeanObject,
    mut v_a_4196_: *mut leanh::LeanObject,
    mut v_a_4197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: u8 = 0;
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v___y_4211_: u32 = 0;
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: u32 = 0;
    let mut v___x_4222_: u32 = 0;
    let mut v___x_4223_: u8 = 0;
    let mut v___x_4224_: u32 = 0;
    let mut v___x_4225_: u32 = 0;
    let mut v___x_4226_: u32 = 0;
    let mut v___x_4227_: u8 = 0;
    let mut v___x_4228_: u32 = 0;
    let mut v___x_4229_: u32 = 0;
    let mut v___x_4230_: u32 = 0;
    let mut v___x_4231_: u32 = 0;
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut v_a_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4238_: u8 = 0;
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4199_ = l_Char_reduceToUpper___redArg___closed__1;
                v___x_4200_ = leanh::lean_unsigned_to_nat(1);
                v___x_4201_ = l_Lean_Expr_isAppOfArity(v_e_4193_, v___x_4199_, v___x_4200_);
                if v___x_4201_ == 0 {
                    v___x_4202_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4203_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4203_, 0, v___x_4202_);
                    return v___x_4203_;
                } else {
                    v___x_4204_ = l_Lean_Expr_appArg_x21(v_e_4193_);
                    v___x_4205_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_4204_,
                        v_a_4194_,
                        v_a_4195_,
                        v_a_4196_,
                        v_a_4197_,
                    );
                    if leanh::lean_obj_tag(v___x_4205_) == 0 {
                        v_a_4206_ = leanh::lean_ctor_get(v___x_4205_, 0);
                        v_isSharedCheck_4234_ =
                            (!leanh::lean_is_exclusive(v___x_4205_)) as u8;
                        if v_isSharedCheck_4234_ == 0 {
                            v___x_4208_ = v___x_4205_;
                            v_isShared_4209_ = v_isSharedCheck_4234_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4206_);
                            leanh::lean_dec(v___x_4205_);
                            v___x_4208_ = leanh::lean_box(0);
                            v_isShared_4209_ = v_isSharedCheck_4234_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4235_ = leanh::lean_ctor_get(v___x_4205_, 0);
                        v_isSharedCheck_4242_ =
                            (!leanh::lean_is_exclusive(v___x_4205_)) as u8;
                        if v_isSharedCheck_4242_ == 0 {
                            v___x_4237_ = v___x_4205_;
                            v_isShared_4238_ = v_isSharedCheck_4242_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4235_);
                            leanh::lean_dec(v___x_4205_);
                            v___x_4237_ = leanh::lean_box(0);
                            v_isShared_4238_ = v_isSharedCheck_4242_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4206_) == 1 {
                    v_val_4220_ = leanh::lean_ctor_get(v_a_4206_, 0);
                    leanh::lean_inc(v_val_4220_);
                    leanh::lean_dec_ref_known(v_a_4206_, 1);
                    v___x_4221_ = 97;
                    v___x_4222_ = leanh::lean_unbox_uint32(v_val_4220_);
                    v___x_4223_ = lean_uint32_dec_le(v___x_4221_, v___x_4222_);
                    if v___x_4223_ == 0 {
                        v___x_4224_ = leanh::lean_unbox_uint32(v_val_4220_);
                        leanh::lean_dec(v_val_4220_);
                        v___y_4211_ = v___x_4224_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4225_ = 122;
                        v___x_4226_ = leanh::lean_unbox_uint32(v_val_4220_);
                        v___x_4227_ = lean_uint32_dec_le(v___x_4226_, v___x_4225_);
                        if v___x_4227_ == 0 {
                            v___x_4228_ = leanh::lean_unbox_uint32(v_val_4220_);
                            leanh::lean_dec(v_val_4220_);
                            v___y_4211_ = v___x_4228_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4229_ = 4294967264;
                            v___x_4230_ = leanh::lean_unbox_uint32(v_val_4220_);
                            leanh::lean_dec(v_val_4220_);
                            v___x_4231_ = lean_uint32_add(v___x_4230_, v___x_4229_);
                            v___y_4211_ = v___x_4231_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4208_);
                    leanh::lean_dec(v_a_4206_);
                    v___x_4232_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4233_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4233_, 0, v___x_4232_);
                    return v___x_4233_;
                }
            }
            2 => {
                v___x_4212_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceToLower___redArg___closed__5),
                    core::ptr::addr_of_mut!(l_Char_reduceToLower___redArg___closed__5_once),
                    _init_l_Char_reduceToLower___redArg___closed__5,
                );
                v___x_4213_ = lean_uint32_to_nat(v___y_4211_);
                v___x_4214_ = l_Lean_mkRawNatLit(v___x_4213_);
                v___x_4215_ = l_Lean_Expr_app___override(v___x_4212_, v___x_4214_);
                v___x_4216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4216_, 0, v___x_4215_);
                if v_isShared_4209_ == 0 {
                    leanh::lean_ctor_set(v___x_4208_, 0, v___x_4216_);
                    v___x_4218_ = v___x_4208_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
                    v___x_4218_ = v_reuseFailAlloc_4219_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4218_;
            }
            4 => {
                if v_isShared_4238_ == 0 {
                    v___x_4240_ = v___x_4237_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
                    v___x_4240_ = v_reuseFailAlloc_4241_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceToUpper___redArg___boxed(
    mut v_e_4243_: *mut leanh::LeanObject,
    mut v_a_4244_: *mut leanh::LeanObject,
    mut v_a_4245_: *mut leanh::LeanObject,
    mut v_a_4246_: *mut leanh::LeanObject,
    mut v_a_4247_: *mut leanh::LeanObject,
    mut v_a_4248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4249_ =
        l_Char_reduceToUpper___redArg(v_e_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_);
    leanh::lean_dec(v_a_4247_);
    leanh::lean_dec_ref(v_a_4246_);
    leanh::lean_dec(v_a_4245_);
    leanh::lean_dec_ref(v_a_4244_);
    leanh::lean_dec_ref(v_e_4243_);
    return v_res_4249_;
}
pub unsafe fn l_Char_reduceToUpper(
    mut v_e_4250_: *mut leanh::LeanObject,
    mut v_a_4251_: *mut leanh::LeanObject,
    mut v_a_4252_: *mut leanh::LeanObject,
    mut v_a_4253_: *mut leanh::LeanObject,
    mut v_a_4254_: *mut leanh::LeanObject,
    mut v_a_4255_: *mut leanh::LeanObject,
    mut v_a_4256_: *mut leanh::LeanObject,
    mut v_a_4257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4259_ =
        l_Char_reduceToUpper___redArg(v_e_4250_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
    return v___x_4259_;
}
pub unsafe fn l_Char_reduceToUpper___boxed(
    mut v_e_4260_: *mut leanh::LeanObject,
    mut v_a_4261_: *mut leanh::LeanObject,
    mut v_a_4262_: *mut leanh::LeanObject,
    mut v_a_4263_: *mut leanh::LeanObject,
    mut v_a_4264_: *mut leanh::LeanObject,
    mut v_a_4265_: *mut leanh::LeanObject,
    mut v_a_4266_: *mut leanh::LeanObject,
    mut v_a_4267_: *mut leanh::LeanObject,
    mut v_a_4268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4269_ = l_Char_reduceToUpper(
        v_e_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_,
    );
    leanh::lean_dec(v_a_4267_);
    leanh::lean_dec_ref(v_a_4266_);
    leanh::lean_dec(v_a_4265_);
    leanh::lean_dec_ref(v_a_4264_);
    leanh::lean_dec(v_a_4263_);
    leanh::lean_dec_ref(v_a_4262_);
    leanh::lean_dec(v_a_4261_);
    leanh::lean_dec_ref(v_e_4260_);
    return v_res_4269_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_;
    v___x_4285_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_;
    v___x_4286_ = leanh::lean_alloc_closure(
        l_Char_reduceToUpper___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4287_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4284_, v___x_4285_, v___x_4286_);
    return v___x_4287_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13____boxed(
    mut v_a_4288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4289_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_();
    return v_res_4289_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4290_ = leanh::lean_alloc_closure(
        l_Char_reduceToUpper___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4291_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4291_, 0, v___x_4290_);
    return v___x_4291_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: u8 = 0;
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_;
    v___x_4294_ = 1;
    v___x_4295_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_);
    v___x_4296_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4293_, v___x_4294_, v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15____boxed(
    mut v_a_4297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4298_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_();
    return v_res_4298_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: u8 = 0;
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4300_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_;
    v___x_4301_ = 1;
    v___x_4302_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_);
    v___x_4303_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4300_, v___x_4301_, v___x_4302_);
    return v___x_4303_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17____boxed(
    mut v_a_4304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4305_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17_();
    return v_res_4305_;
}
pub unsafe fn l_Char_reduceToNat___redArg(
    mut v_e_4310_: *mut leanh::LeanObject,
    mut v_a_4311_: *mut leanh::LeanObject,
    mut v_a_4312_: *mut leanh::LeanObject,
    mut v_a_4313_: *mut leanh::LeanObject,
    mut v_a_4314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: u8 = 0;
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v_val_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4330_: u8 = 0;
    let mut v___x_4331_: u32 = 0;
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v_a_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4316_ = l_Char_reduceToNat___redArg___closed__1;
                v___x_4317_ = leanh::lean_unsigned_to_nat(1);
                v___x_4318_ = l_Lean_Expr_isAppOfArity(v_e_4310_, v___x_4316_, v___x_4317_);
                if v___x_4318_ == 0 {
                    v___x_4319_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4320_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4319_);
                    return v___x_4320_;
                } else {
                    v___x_4321_ = l_Lean_Expr_appArg_x21(v_e_4310_);
                    v___x_4322_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_4321_,
                        v_a_4311_,
                        v_a_4312_,
                        v_a_4313_,
                        v_a_4314_,
                    );
                    if leanh::lean_obj_tag(v___x_4322_) == 0 {
                        v_a_4323_ = leanh::lean_ctor_get(v___x_4322_, 0);
                        v_isSharedCheck_4345_ =
                            (!leanh::lean_is_exclusive(v___x_4322_)) as u8;
                        if v_isSharedCheck_4345_ == 0 {
                            v___x_4325_ = v___x_4322_;
                            v_isShared_4326_ = v_isSharedCheck_4345_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4323_);
                            leanh::lean_dec(v___x_4322_);
                            v___x_4325_ = leanh::lean_box(0);
                            v_isShared_4326_ = v_isSharedCheck_4345_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4346_ = leanh::lean_ctor_get(v___x_4322_, 0);
                        v_isSharedCheck_4353_ =
                            (!leanh::lean_is_exclusive(v___x_4322_)) as u8;
                        if v_isSharedCheck_4353_ == 0 {
                            v___x_4348_ = v___x_4322_;
                            v_isShared_4349_ = v_isSharedCheck_4353_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4346_);
                            leanh::lean_dec(v___x_4322_);
                            v___x_4348_ = leanh::lean_box(0);
                            v_isShared_4349_ = v_isSharedCheck_4353_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4323_) == 1 {
                    v_val_4327_ = leanh::lean_ctor_get(v_a_4323_, 0);
                    v_isSharedCheck_4340_ = (!leanh::lean_is_exclusive(v_a_4323_)) as u8;
                    if v_isSharedCheck_4340_ == 0 {
                        v___x_4329_ = v_a_4323_;
                        v_isShared_4330_ = v_isSharedCheck_4340_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4327_);
                        leanh::lean_dec(v_a_4323_);
                        v___x_4329_ = leanh::lean_box(0);
                        v_isShared_4330_ = v_isSharedCheck_4340_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4323_);
                    v___x_4341_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_4326_ == 0 {
                        leanh::lean_ctor_set(v___x_4325_, 0, v___x_4341_);
                        v___x_4343_ = v___x_4325_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4344_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
                        v___x_4343_ = v_reuseFailAlloc_4344_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4331_ = leanh::lean_unbox_uint32(v_val_4327_);
                leanh::lean_dec(v_val_4327_);
                v___x_4332_ = lean_uint32_to_nat(v___x_4331_);
                v___x_4333_ = l_Lean_mkNatLit(v___x_4332_);
                if v_isShared_4330_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4329_, 0);
                    leanh::lean_ctor_set(v___x_4329_, 0, v___x_4333_);
                    v___x_4335_ = v___x_4329_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4339_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4333_);
                    v___x_4335_ = v_reuseFailAlloc_4339_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4326_ == 0 {
                    leanh::lean_ctor_set(v___x_4325_, 0, v___x_4335_);
                    v___x_4337_ = v___x_4325_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4338_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4335_);
                    v___x_4337_ = v_reuseFailAlloc_4338_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4337_;
            }
            5 => {
                return v___x_4343_;
            }
            6 => {
                if v_isShared_4349_ == 0 {
                    v___x_4351_ = v___x_4348_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4352_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
                    v___x_4351_ = v_reuseFailAlloc_4352_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceToNat___redArg___boxed(
    mut v_e_4354_: *mut leanh::LeanObject,
    mut v_a_4355_: *mut leanh::LeanObject,
    mut v_a_4356_: *mut leanh::LeanObject,
    mut v_a_4357_: *mut leanh::LeanObject,
    mut v_a_4358_: *mut leanh::LeanObject,
    mut v_a_4359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4360_ =
        l_Char_reduceToNat___redArg(v_e_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
    leanh::lean_dec(v_a_4358_);
    leanh::lean_dec_ref(v_a_4357_);
    leanh::lean_dec(v_a_4356_);
    leanh::lean_dec_ref(v_a_4355_);
    leanh::lean_dec_ref(v_e_4354_);
    return v_res_4360_;
}
pub unsafe fn l_Char_reduceToNat(
    mut v_e_4361_: *mut leanh::LeanObject,
    mut v_a_4362_: *mut leanh::LeanObject,
    mut v_a_4363_: *mut leanh::LeanObject,
    mut v_a_4364_: *mut leanh::LeanObject,
    mut v_a_4365_: *mut leanh::LeanObject,
    mut v_a_4366_: *mut leanh::LeanObject,
    mut v_a_4367_: *mut leanh::LeanObject,
    mut v_a_4368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4370_ =
        l_Char_reduceToNat___redArg(v_e_4361_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
    return v___x_4370_;
}
pub unsafe fn l_Char_reduceToNat___boxed(
    mut v_e_4371_: *mut leanh::LeanObject,
    mut v_a_4372_: *mut leanh::LeanObject,
    mut v_a_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
    mut v_a_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
    mut v_a_4377_: *mut leanh::LeanObject,
    mut v_a_4378_: *mut leanh::LeanObject,
    mut v_a_4379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4380_ = l_Char_reduceToNat(
        v_e_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_,
    );
    leanh::lean_dec(v_a_4378_);
    leanh::lean_dec_ref(v_a_4377_);
    leanh::lean_dec(v_a_4376_);
    leanh::lean_dec_ref(v_a_4375_);
    leanh::lean_dec(v_a_4374_);
    leanh::lean_dec_ref(v_a_4373_);
    leanh::lean_dec(v_a_4372_);
    leanh::lean_dec_ref(v_e_4371_);
    return v_res_4380_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4395_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_;
    v___x_4396_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_;
    v___x_4397_ = leanh::lean_alloc_closure(
        l_Char_reduceToNat___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4398_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4395_, v___x_4396_, v___x_4397_);
    return v___x_4398_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13____boxed(
    mut v_a_4399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4400_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_();
    return v_res_4400_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4401_ = leanh::lean_alloc_closure(
        l_Char_reduceToNat___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4402_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4402_, 0, v___x_4401_);
    return v___x_4402_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: u8 = 0;
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4404_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_;
    v___x_4405_ = 1;
    v___x_4406_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_);
    v___x_4407_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4404_, v___x_4405_, v___x_4406_);
    return v___x_4407_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15____boxed(
    mut v_a_4408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_();
    return v_res_4409_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4411_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_;
    v___x_4412_ = 1;
    v___x_4413_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_);
    v___x_4414_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4411_, v___x_4412_, v___x_4413_);
    return v___x_4414_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17____boxed(
    mut v_a_4415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4416_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17_();
    return v_res_4416_;
}
pub unsafe fn l_Char_reduceIsWhitespace___redArg(
    mut v_e_4421_: *mut leanh::LeanObject,
    mut v_a_4422_: *mut leanh::LeanObject,
    mut v_a_4423_: *mut leanh::LeanObject,
    mut v_a_4424_: *mut leanh::LeanObject,
    mut v_a_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: u8 = 0;
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___y_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4447_: u8 = 0;
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4451_: u8 = 0;
    let mut v___x_4452_: u32 = 0;
    let mut v___x_4453_: u32 = 0;
    let mut v___x_4454_: u8 = 0;
    let mut v___x_4455_: u32 = 0;
    let mut v___x_4456_: u32 = 0;
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4458_: u32 = 0;
    let mut v___x_4459_: u32 = 0;
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: u32 = 0;
    let mut v___x_4462_: u32 = 0;
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v_a_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4470_: u8 = 0;
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4427_ = l_Char_reduceIsWhitespace___redArg___closed__1;
                v___x_4428_ = leanh::lean_unsigned_to_nat(1);
                v___x_4429_ = l_Lean_Expr_isAppOfArity(v_e_4421_, v___x_4427_, v___x_4428_);
                if v___x_4429_ == 0 {
                    v___x_4430_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4431_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4431_, 0, v___x_4430_);
                    return v___x_4431_;
                } else {
                    v___x_4432_ = l_Lean_Expr_appArg_x21(v_e_4421_);
                    v___x_4433_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_4432_,
                        v_a_4422_,
                        v_a_4423_,
                        v_a_4424_,
                        v_a_4425_,
                    );
                    if leanh::lean_obj_tag(v___x_4433_) == 0 {
                        v_a_4434_ = leanh::lean_ctor_get(v___x_4433_, 0);
                        v_isSharedCheck_4466_ =
                            (!leanh::lean_is_exclusive(v___x_4433_)) as u8;
                        if v_isSharedCheck_4466_ == 0 {
                            v___x_4436_ = v___x_4433_;
                            v_isShared_4437_ = v_isSharedCheck_4466_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4434_);
                            leanh::lean_dec(v___x_4433_);
                            v___x_4436_ = leanh::lean_box(0);
                            v_isShared_4437_ = v_isSharedCheck_4466_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4467_ = leanh::lean_ctor_get(v___x_4433_, 0);
                        v_isSharedCheck_4474_ =
                            (!leanh::lean_is_exclusive(v___x_4433_)) as u8;
                        if v_isSharedCheck_4474_ == 0 {
                            v___x_4469_ = v___x_4433_;
                            v_isShared_4470_ = v_isSharedCheck_4474_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4467_);
                            leanh::lean_dec(v___x_4433_);
                            v___x_4469_ = leanh::lean_box(0);
                            v_isShared_4470_ = v_isSharedCheck_4474_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4434_) == 1 {
                    v_val_4449_ = leanh::lean_ctor_get(v_a_4434_, 0);
                    leanh::lean_inc(v_val_4449_);
                    leanh::lean_dec_ref_known(v_a_4434_, 1);
                    v___x_4458_ = 32;
                    v___x_4459_ = leanh::lean_unbox_uint32(v_val_4449_);
                    v___x_4460_ = lean_uint32_dec_eq(v___x_4459_, v___x_4458_);
                    if v___x_4460_ == 0 {
                        v___x_4461_ = 9;
                        v___x_4462_ = leanh::lean_unbox_uint32(v_val_4449_);
                        v___x_4463_ = lean_uint32_dec_eq(v___x_4462_, v___x_4461_);
                        v___y_4451_ = v___x_4463_;
                        state = 6;
                        continue;
                    } else {
                        v___y_4451_ = v___x_4460_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4436_);
                    leanh::lean_dec(v_a_4434_);
                    v___x_4464_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4465_, 0, v___x_4464_);
                    return v___x_4465_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___y_4439_);
                v___x_4440_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4440_, 0, v___y_4439_);
                if v_isShared_4437_ == 0 {
                    leanh::lean_ctor_set(v___x_4436_, 0, v___x_4440_);
                    v___x_4442_ = v___x_4436_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4443_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
                    v___x_4442_ = v_reuseFailAlloc_4443_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4442_;
            }
            4 => {
                v___x_4445_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                    core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6_once),
                    _init_l_Char_reduceBoolPred___redArg___closed__6,
                );
                v___y_4439_ = v___x_4445_;
                state = 2;
                continue;
            }
            5 => {
                if v___y_4447_ == 0 {
                    v___x_4448_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3_once),
                        _init_l_Char_reduceBoolPred___redArg___closed__3,
                    );
                    v___y_4439_ = v___x_4448_;
                    state = 2;
                    continue;
                } else {
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v___y_4451_ == 0 {
                    v___x_4452_ = 13;
                    v___x_4453_ = leanh::lean_unbox_uint32(v_val_4449_);
                    v___x_4454_ = lean_uint32_dec_eq(v___x_4453_, v___x_4452_);
                    if v___x_4454_ == 0 {
                        v___x_4455_ = 10;
                        v___x_4456_ = leanh::lean_unbox_uint32(v_val_4449_);
                        leanh::lean_dec(v_val_4449_);
                        v___x_4457_ = lean_uint32_dec_eq(v___x_4456_, v___x_4455_);
                        v___y_4447_ = v___x_4457_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_4449_);
                        v___y_4447_ = v___x_4454_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_val_4449_);
                    state = 4;
                    continue;
                }
            }
            7 => {
                if v_isShared_4470_ == 0 {
                    v___x_4472_ = v___x_4469_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
                    v___x_4472_ = v_reuseFailAlloc_4473_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceIsWhitespace___redArg___boxed(
    mut v_e_4475_: *mut leanh::LeanObject,
    mut v_a_4476_: *mut leanh::LeanObject,
    mut v_a_4477_: *mut leanh::LeanObject,
    mut v_a_4478_: *mut leanh::LeanObject,
    mut v_a_4479_: *mut leanh::LeanObject,
    mut v_a_4480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ =
        l_Char_reduceIsWhitespace___redArg(v_e_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
    leanh::lean_dec(v_a_4479_);
    leanh::lean_dec_ref(v_a_4478_);
    leanh::lean_dec(v_a_4477_);
    leanh::lean_dec_ref(v_a_4476_);
    leanh::lean_dec_ref(v_e_4475_);
    return v_res_4481_;
}
pub unsafe fn l_Char_reduceIsWhitespace(
    mut v_e_4482_: *mut leanh::LeanObject,
    mut v_a_4483_: *mut leanh::LeanObject,
    mut v_a_4484_: *mut leanh::LeanObject,
    mut v_a_4485_: *mut leanh::LeanObject,
    mut v_a_4486_: *mut leanh::LeanObject,
    mut v_a_4487_: *mut leanh::LeanObject,
    mut v_a_4488_: *mut leanh::LeanObject,
    mut v_a_4489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4491_ =
        l_Char_reduceIsWhitespace___redArg(v_e_4482_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_);
    return v___x_4491_;
}
pub unsafe fn l_Char_reduceIsWhitespace___boxed(
    mut v_e_4492_: *mut leanh::LeanObject,
    mut v_a_4493_: *mut leanh::LeanObject,
    mut v_a_4494_: *mut leanh::LeanObject,
    mut v_a_4495_: *mut leanh::LeanObject,
    mut v_a_4496_: *mut leanh::LeanObject,
    mut v_a_4497_: *mut leanh::LeanObject,
    mut v_a_4498_: *mut leanh::LeanObject,
    mut v_a_4499_: *mut leanh::LeanObject,
    mut v_a_4500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4501_ = l_Char_reduceIsWhitespace(
        v_e_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_,
    );
    leanh::lean_dec(v_a_4499_);
    leanh::lean_dec_ref(v_a_4498_);
    leanh::lean_dec(v_a_4497_);
    leanh::lean_dec_ref(v_a_4496_);
    leanh::lean_dec(v_a_4495_);
    leanh::lean_dec_ref(v_a_4494_);
    leanh::lean_dec(v_a_4493_);
    leanh::lean_dec_ref(v_e_4492_);
    return v_res_4501_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4516_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_;
    v___x_4517_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_;
    v___x_4518_ = leanh::lean_alloc_closure(
        l_Char_reduceIsWhitespace___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4519_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4516_, v___x_4517_, v___x_4518_);
    return v___x_4519_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13____boxed(
    mut v_a_4520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4521_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_();
    return v_res_4521_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4522_ = leanh::lean_alloc_closure(
        l_Char_reduceIsWhitespace___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4523_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4523_, 0, v___x_4522_);
    return v___x_4523_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: u8 = 0;
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4525_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_;
    v___x_4526_ = 1;
    v___x_4527_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_);
    v___x_4528_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4525_, v___x_4526_, v___x_4527_);
    return v___x_4528_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15____boxed(
    mut v_a_4529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4530_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_();
    return v_res_4530_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4532_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_;
    v___x_4533_ = 1;
    v___x_4534_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_);
    v___x_4535_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4532_, v___x_4533_, v___x_4534_);
    return v___x_4535_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17____boxed(
    mut v_a_4536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4537_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17_();
    return v_res_4537_;
}
pub unsafe fn l_Char_reduceIsUpper___redArg(
    mut v_e_4542_: *mut leanh::LeanObject,
    mut v_a_4543_: *mut leanh::LeanObject,
    mut v_a_4544_: *mut leanh::LeanObject,
    mut v_a_4545_: *mut leanh::LeanObject,
    mut v_a_4546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: u8 = 0;
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4558_: u8 = 0;
    let mut v___y_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: u32 = 0;
    let mut v___x_4569_: u32 = 0;
    let mut v___x_4570_: u8 = 0;
    let mut v___x_4571_: u32 = 0;
    let mut v___x_4572_: u32 = 0;
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4577_: u8 = 0;
    let mut v_a_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4548_ = l_Char_reduceIsUpper___redArg___closed__1;
                v___x_4549_ = leanh::lean_unsigned_to_nat(1);
                v___x_4550_ = l_Lean_Expr_isAppOfArity(v_e_4542_, v___x_4548_, v___x_4549_);
                if v___x_4550_ == 0 {
                    v___x_4551_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4552_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4552_, 0, v___x_4551_);
                    return v___x_4552_;
                } else {
                    v___x_4553_ = l_Lean_Expr_appArg_x21(v_e_4542_);
                    v___x_4554_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_4553_,
                        v_a_4543_,
                        v_a_4544_,
                        v_a_4545_,
                        v_a_4546_,
                    );
                    if leanh::lean_obj_tag(v___x_4554_) == 0 {
                        v_a_4555_ = leanh::lean_ctor_get(v___x_4554_, 0);
                        v_isSharedCheck_4577_ =
                            (!leanh::lean_is_exclusive(v___x_4554_)) as u8;
                        if v_isSharedCheck_4577_ == 0 {
                            v___x_4557_ = v___x_4554_;
                            v_isShared_4558_ = v_isSharedCheck_4577_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4555_);
                            leanh::lean_dec(v___x_4554_);
                            v___x_4557_ = leanh::lean_box(0);
                            v_isShared_4558_ = v_isSharedCheck_4577_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4578_ = leanh::lean_ctor_get(v___x_4554_, 0);
                        v_isSharedCheck_4585_ =
                            (!leanh::lean_is_exclusive(v___x_4554_)) as u8;
                        if v_isSharedCheck_4585_ == 0 {
                            v___x_4580_ = v___x_4554_;
                            v_isShared_4581_ = v_isSharedCheck_4585_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4578_);
                            leanh::lean_dec(v___x_4554_);
                            v___x_4580_ = leanh::lean_box(0);
                            v_isShared_4581_ = v_isSharedCheck_4585_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4555_) == 1 {
                    v_val_4567_ = leanh::lean_ctor_get(v_a_4555_, 0);
                    leanh::lean_inc(v_val_4567_);
                    leanh::lean_dec_ref_known(v_a_4555_, 1);
                    v___x_4568_ = 65;
                    v___x_4569_ = leanh::lean_unbox_uint32(v_val_4567_);
                    v___x_4570_ = lean_uint32_dec_le(v___x_4568_, v___x_4569_);
                    if v___x_4570_ == 0 {
                        leanh::lean_dec(v_val_4567_);
                        state = 4;
                        continue;
                    } else {
                        v___x_4571_ = 90;
                        v___x_4572_ = leanh::lean_unbox_uint32(v_val_4567_);
                        leanh::lean_dec(v_val_4567_);
                        v___x_4573_ = lean_uint32_dec_le(v___x_4572_, v___x_4571_);
                        if v___x_4573_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            if v___x_4550_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                v___x_4574_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Char_reduceBoolPred___redArg___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Char_reduceBoolPred___redArg___closed__6_once
                                    ),
                                    _init_l_Char_reduceBoolPred___redArg___closed__6,
                                );
                                v___y_4560_ = v___x_4574_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4557_);
                    leanh::lean_dec(v_a_4555_);
                    v___x_4575_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4576_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4576_, 0, v___x_4575_);
                    return v___x_4576_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___y_4560_);
                v___x_4561_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4561_, 0, v___y_4560_);
                if v_isShared_4558_ == 0 {
                    leanh::lean_ctor_set(v___x_4557_, 0, v___x_4561_);
                    v___x_4563_ = v___x_4557_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
                    v___x_4563_ = v_reuseFailAlloc_4564_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4563_;
            }
            4 => {
                v___x_4566_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3_once),
                    _init_l_Char_reduceBoolPred___redArg___closed__3,
                );
                v___y_4560_ = v___x_4566_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_4581_ == 0 {
                    v___x_4583_ = v___x_4580_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4578_);
                    v___x_4583_ = v_reuseFailAlloc_4584_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceIsUpper___redArg___boxed(
    mut v_e_4586_: *mut leanh::LeanObject,
    mut v_a_4587_: *mut leanh::LeanObject,
    mut v_a_4588_: *mut leanh::LeanObject,
    mut v_a_4589_: *mut leanh::LeanObject,
    mut v_a_4590_: *mut leanh::LeanObject,
    mut v_a_4591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4592_ =
        l_Char_reduceIsUpper___redArg(v_e_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
    leanh::lean_dec(v_a_4590_);
    leanh::lean_dec_ref(v_a_4589_);
    leanh::lean_dec(v_a_4588_);
    leanh::lean_dec_ref(v_a_4587_);
    leanh::lean_dec_ref(v_e_4586_);
    return v_res_4592_;
}
pub unsafe fn l_Char_reduceIsUpper(
    mut v_e_4593_: *mut leanh::LeanObject,
    mut v_a_4594_: *mut leanh::LeanObject,
    mut v_a_4595_: *mut leanh::LeanObject,
    mut v_a_4596_: *mut leanh::LeanObject,
    mut v_a_4597_: *mut leanh::LeanObject,
    mut v_a_4598_: *mut leanh::LeanObject,
    mut v_a_4599_: *mut leanh::LeanObject,
    mut v_a_4600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4602_ =
        l_Char_reduceIsUpper___redArg(v_e_4593_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
    return v___x_4602_;
}
pub unsafe fn l_Char_reduceIsUpper___boxed(
    mut v_e_4603_: *mut leanh::LeanObject,
    mut v_a_4604_: *mut leanh::LeanObject,
    mut v_a_4605_: *mut leanh::LeanObject,
    mut v_a_4606_: *mut leanh::LeanObject,
    mut v_a_4607_: *mut leanh::LeanObject,
    mut v_a_4608_: *mut leanh::LeanObject,
    mut v_a_4609_: *mut leanh::LeanObject,
    mut v_a_4610_: *mut leanh::LeanObject,
    mut v_a_4611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4612_ = l_Char_reduceIsUpper(
        v_e_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_,
    );
    leanh::lean_dec(v_a_4610_);
    leanh::lean_dec_ref(v_a_4609_);
    leanh::lean_dec(v_a_4608_);
    leanh::lean_dec_ref(v_a_4607_);
    leanh::lean_dec(v_a_4606_);
    leanh::lean_dec_ref(v_a_4605_);
    leanh::lean_dec(v_a_4604_);
    leanh::lean_dec_ref(v_e_4603_);
    return v_res_4612_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4627_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_;
    v___x_4628_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_;
    v___x_4629_ = leanh::lean_alloc_closure(
        l_Char_reduceIsUpper___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4630_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4627_, v___x_4628_, v___x_4629_);
    return v___x_4630_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13____boxed(
    mut v_a_4631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4632_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_();
    return v_res_4632_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4633_ = leanh::lean_alloc_closure(
        l_Char_reduceIsUpper___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4634_, 0, v___x_4633_);
    return v___x_4634_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: u8 = 0;
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_;
    v___x_4637_ = 1;
    v___x_4638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_);
    v___x_4639_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4636_, v___x_4637_, v___x_4638_);
    return v___x_4639_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15____boxed(
    mut v_a_4640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4641_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_();
    return v_res_4641_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: u8 = 0;
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4643_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_;
    v___x_4644_ = 1;
    v___x_4645_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_);
    v___x_4646_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4643_, v___x_4644_, v___x_4645_);
    return v___x_4646_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17____boxed(
    mut v_a_4647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4648_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17_();
    return v_res_4648_;
}
pub unsafe fn l_Char_reduceIsLower___redArg(
    mut v_e_4653_: *mut leanh::LeanObject,
    mut v_a_4654_: *mut leanh::LeanObject,
    mut v_a_4655_: *mut leanh::LeanObject,
    mut v_a_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: u8 = 0;
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4669_: u8 = 0;
    let mut v___y_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4677_: u8 = 0;
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: u32 = 0;
    let mut v___x_4682_: u32 = 0;
    let mut v___x_4683_: u8 = 0;
    let mut v___x_4684_: u32 = 0;
    let mut v___x_4685_: u32 = 0;
    let mut v___x_4686_: u8 = 0;
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v_a_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4693_: u8 = 0;
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4659_ = l_Char_reduceIsLower___redArg___closed__1;
                v___x_4660_ = leanh::lean_unsigned_to_nat(1);
                v___x_4661_ = l_Lean_Expr_isAppOfArity(v_e_4653_, v___x_4659_, v___x_4660_);
                if v___x_4661_ == 0 {
                    v___x_4662_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4663_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4663_, 0, v___x_4662_);
                    return v___x_4663_;
                } else {
                    v___x_4664_ = l_Lean_Expr_appArg_x21(v_e_4653_);
                    v___x_4665_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_4664_,
                        v_a_4654_,
                        v_a_4655_,
                        v_a_4656_,
                        v_a_4657_,
                    );
                    if leanh::lean_obj_tag(v___x_4665_) == 0 {
                        v_a_4666_ = leanh::lean_ctor_get(v___x_4665_, 0);
                        v_isSharedCheck_4689_ =
                            (!leanh::lean_is_exclusive(v___x_4665_)) as u8;
                        if v_isSharedCheck_4689_ == 0 {
                            v___x_4668_ = v___x_4665_;
                            v_isShared_4669_ = v_isSharedCheck_4689_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4666_);
                            leanh::lean_dec(v___x_4665_);
                            v___x_4668_ = leanh::lean_box(0);
                            v_isShared_4669_ = v_isSharedCheck_4689_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4690_ = leanh::lean_ctor_get(v___x_4665_, 0);
                        v_isSharedCheck_4697_ =
                            (!leanh::lean_is_exclusive(v___x_4665_)) as u8;
                        if v_isSharedCheck_4697_ == 0 {
                            v___x_4692_ = v___x_4665_;
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4690_);
                            leanh::lean_dec(v___x_4665_);
                            v___x_4692_ = leanh::lean_box(0);
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4666_) == 1 {
                    v_val_4680_ = leanh::lean_ctor_get(v_a_4666_, 0);
                    leanh::lean_inc(v_val_4680_);
                    leanh::lean_dec_ref_known(v_a_4666_, 1);
                    v___x_4681_ = 97;
                    v___x_4682_ = leanh::lean_unbox_uint32(v_val_4680_);
                    v___x_4683_ = lean_uint32_dec_le(v___x_4681_, v___x_4682_);
                    if v___x_4683_ == 0 {
                        leanh::lean_dec(v_val_4680_);
                        v___y_4677_ = v___x_4683_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4684_ = 122;
                        v___x_4685_ = leanh::lean_unbox_uint32(v_val_4680_);
                        leanh::lean_dec(v_val_4680_);
                        v___x_4686_ = lean_uint32_dec_le(v___x_4685_, v___x_4684_);
                        v___y_4677_ = v___x_4686_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4668_);
                    leanh::lean_dec(v_a_4666_);
                    v___x_4687_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4688_, 0, v___x_4687_);
                    return v___x_4688_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___y_4671_);
                v___x_4672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4672_, 0, v___y_4671_);
                if v_isShared_4669_ == 0 {
                    leanh::lean_ctor_set(v___x_4668_, 0, v___x_4672_);
                    v___x_4674_ = v___x_4668_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4672_);
                    v___x_4674_ = v_reuseFailAlloc_4675_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4674_;
            }
            4 => {
                if v___y_4677_ == 0 {
                    v___x_4678_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3_once),
                        _init_l_Char_reduceBoolPred___redArg___closed__3,
                    );
                    v___y_4671_ = v___x_4678_;
                    state = 2;
                    continue;
                } else {
                    v___x_4679_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6_once),
                        _init_l_Char_reduceBoolPred___redArg___closed__6,
                    );
                    v___y_4671_ = v___x_4679_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_4693_ == 0 {
                    v___x_4695_ = v___x_4692_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
                    v___x_4695_ = v_reuseFailAlloc_4696_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceIsLower___redArg___boxed(
    mut v_e_4698_: *mut leanh::LeanObject,
    mut v_a_4699_: *mut leanh::LeanObject,
    mut v_a_4700_: *mut leanh::LeanObject,
    mut v_a_4701_: *mut leanh::LeanObject,
    mut v_a_4702_: *mut leanh::LeanObject,
    mut v_a_4703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4704_ =
        l_Char_reduceIsLower___redArg(v_e_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
    leanh::lean_dec(v_a_4702_);
    leanh::lean_dec_ref(v_a_4701_);
    leanh::lean_dec(v_a_4700_);
    leanh::lean_dec_ref(v_a_4699_);
    leanh::lean_dec_ref(v_e_4698_);
    return v_res_4704_;
}
pub unsafe fn l_Char_reduceIsLower(
    mut v_e_4705_: *mut leanh::LeanObject,
    mut v_a_4706_: *mut leanh::LeanObject,
    mut v_a_4707_: *mut leanh::LeanObject,
    mut v_a_4708_: *mut leanh::LeanObject,
    mut v_a_4709_: *mut leanh::LeanObject,
    mut v_a_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4714_ =
        l_Char_reduceIsLower___redArg(v_e_4705_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
    return v___x_4714_;
}
pub unsafe fn l_Char_reduceIsLower___boxed(
    mut v_e_4715_: *mut leanh::LeanObject,
    mut v_a_4716_: *mut leanh::LeanObject,
    mut v_a_4717_: *mut leanh::LeanObject,
    mut v_a_4718_: *mut leanh::LeanObject,
    mut v_a_4719_: *mut leanh::LeanObject,
    mut v_a_4720_: *mut leanh::LeanObject,
    mut v_a_4721_: *mut leanh::LeanObject,
    mut v_a_4722_: *mut leanh::LeanObject,
    mut v_a_4723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4724_ = l_Char_reduceIsLower(
        v_e_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_,
    );
    leanh::lean_dec(v_a_4722_);
    leanh::lean_dec_ref(v_a_4721_);
    leanh::lean_dec(v_a_4720_);
    leanh::lean_dec_ref(v_a_4719_);
    leanh::lean_dec(v_a_4718_);
    leanh::lean_dec_ref(v_a_4717_);
    leanh::lean_dec(v_a_4716_);
    leanh::lean_dec_ref(v_e_4715_);
    return v_res_4724_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4739_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_;
    v___x_4740_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_;
    v___x_4741_ = leanh::lean_alloc_closure(
        l_Char_reduceIsLower___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4742_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4739_, v___x_4740_, v___x_4741_);
    return v___x_4742_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13____boxed(
    mut v_a_4743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4744_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_();
    return v_res_4744_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4745_ = leanh::lean_alloc_closure(
        l_Char_reduceIsLower___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4746_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4746_, 0, v___x_4745_);
    return v___x_4746_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: u8 = 0;
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4748_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_;
    v___x_4749_ = 1;
    v___x_4750_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_);
    v___x_4751_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4748_, v___x_4749_, v___x_4750_);
    return v___x_4751_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15____boxed(
    mut v_a_4752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4753_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_();
    return v_res_4753_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: u8 = 0;
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4755_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_;
    v___x_4756_ = 1;
    v___x_4757_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_);
    v___x_4758_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4755_, v___x_4756_, v___x_4757_);
    return v___x_4758_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17____boxed(
    mut v_a_4759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4760_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17_();
    return v_res_4760_;
}
pub unsafe fn l_Char_reduceIsAlpha___redArg(
    mut v_e_4765_: *mut leanh::LeanObject,
    mut v_a_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
    mut v_a_4768_: *mut leanh::LeanObject,
    mut v_a_4769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4781_: u8 = 0;
    let mut v___y_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4789_: u8 = 0;
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: u32 = 0;
    let mut v___x_4795_: u32 = 0;
    let mut v___x_4796_: u8 = 0;
    let mut v___x_4797_: u32 = 0;
    let mut v___x_4798_: u32 = 0;
    let mut v___x_4799_: u8 = 0;
    let mut v___x_4800_: u32 = 0;
    let mut v___x_4801_: u32 = 0;
    let mut v___x_4802_: u8 = 0;
    let mut v___x_4803_: u32 = 0;
    let mut v___x_4804_: u32 = 0;
    let mut v___x_4805_: u8 = 0;
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v_a_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4812_: u8 = 0;
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4771_ = l_Char_reduceIsAlpha___redArg___closed__1;
                v___x_4772_ = leanh::lean_unsigned_to_nat(1);
                v___x_4773_ = l_Lean_Expr_isAppOfArity(v_e_4765_, v___x_4771_, v___x_4772_);
                if v___x_4773_ == 0 {
                    v___x_4774_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4775_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4775_, 0, v___x_4774_);
                    return v___x_4775_;
                } else {
                    v___x_4776_ = l_Lean_Expr_appArg_x21(v_e_4765_);
                    v___x_4777_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_4776_,
                        v_a_4766_,
                        v_a_4767_,
                        v_a_4768_,
                        v_a_4769_,
                    );
                    if leanh::lean_obj_tag(v___x_4777_) == 0 {
                        v_a_4778_ = leanh::lean_ctor_get(v___x_4777_, 0);
                        v_isSharedCheck_4808_ =
                            (!leanh::lean_is_exclusive(v___x_4777_)) as u8;
                        if v_isSharedCheck_4808_ == 0 {
                            v___x_4780_ = v___x_4777_;
                            v_isShared_4781_ = v_isSharedCheck_4808_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4778_);
                            leanh::lean_dec(v___x_4777_);
                            v___x_4780_ = leanh::lean_box(0);
                            v_isShared_4781_ = v_isSharedCheck_4808_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4809_ = leanh::lean_ctor_get(v___x_4777_, 0);
                        v_isSharedCheck_4816_ =
                            (!leanh::lean_is_exclusive(v___x_4777_)) as u8;
                        if v_isSharedCheck_4816_ == 0 {
                            v___x_4811_ = v___x_4777_;
                            v_isShared_4812_ = v_isSharedCheck_4816_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4809_);
                            leanh::lean_dec(v___x_4777_);
                            v___x_4811_ = leanh::lean_box(0);
                            v_isShared_4812_ = v_isSharedCheck_4816_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4778_) == 1 {
                    v_val_4792_ = leanh::lean_ctor_get(v_a_4778_, 0);
                    leanh::lean_inc(v_val_4792_);
                    leanh::lean_dec_ref_known(v_a_4778_, 1);
                    v___x_4800_ = 65;
                    v___x_4801_ = leanh::lean_unbox_uint32(v_val_4792_);
                    v___x_4802_ = lean_uint32_dec_le(v___x_4800_, v___x_4801_);
                    if v___x_4802_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        v___x_4803_ = 90;
                        v___x_4804_ = leanh::lean_unbox_uint32(v_val_4792_);
                        v___x_4805_ = lean_uint32_dec_le(v___x_4804_, v___x_4803_);
                        if v___x_4805_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_4792_);
                            v___y_4789_ = v___x_4773_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4780_);
                    leanh::lean_dec(v_a_4778_);
                    v___x_4806_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4807_, 0, v___x_4806_);
                    return v___x_4807_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___y_4783_);
                v___x_4784_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4784_, 0, v___y_4783_);
                if v_isShared_4781_ == 0 {
                    leanh::lean_ctor_set(v___x_4780_, 0, v___x_4784_);
                    v___x_4786_ = v___x_4780_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4787_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
                    v___x_4786_ = v_reuseFailAlloc_4787_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4786_;
            }
            4 => {
                if v___y_4789_ == 0 {
                    v___x_4790_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3_once),
                        _init_l_Char_reduceBoolPred___redArg___closed__3,
                    );
                    v___y_4783_ = v___x_4790_;
                    state = 2;
                    continue;
                } else {
                    v___x_4791_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6_once),
                        _init_l_Char_reduceBoolPred___redArg___closed__6,
                    );
                    v___y_4783_ = v___x_4791_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_4794_ = 97;
                v___x_4795_ = leanh::lean_unbox_uint32(v_val_4792_);
                v___x_4796_ = lean_uint32_dec_le(v___x_4794_, v___x_4795_);
                if v___x_4796_ == 0 {
                    leanh::lean_dec(v_val_4792_);
                    v___y_4789_ = v___x_4796_;
                    state = 4;
                    continue;
                } else {
                    v___x_4797_ = 122;
                    v___x_4798_ = leanh::lean_unbox_uint32(v_val_4792_);
                    leanh::lean_dec(v_val_4792_);
                    v___x_4799_ = lean_uint32_dec_le(v___x_4798_, v___x_4797_);
                    v___y_4789_ = v___x_4799_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_4812_ == 0 {
                    v___x_4814_ = v___x_4811_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4815_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4809_);
                    v___x_4814_ = v_reuseFailAlloc_4815_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceIsAlpha___redArg___boxed(
    mut v_e_4817_: *mut leanh::LeanObject,
    mut v_a_4818_: *mut leanh::LeanObject,
    mut v_a_4819_: *mut leanh::LeanObject,
    mut v_a_4820_: *mut leanh::LeanObject,
    mut v_a_4821_: *mut leanh::LeanObject,
    mut v_a_4822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4823_ =
        l_Char_reduceIsAlpha___redArg(v_e_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_);
    leanh::lean_dec(v_a_4821_);
    leanh::lean_dec_ref(v_a_4820_);
    leanh::lean_dec(v_a_4819_);
    leanh::lean_dec_ref(v_a_4818_);
    leanh::lean_dec_ref(v_e_4817_);
    return v_res_4823_;
}
pub unsafe fn l_Char_reduceIsAlpha(
    mut v_e_4824_: *mut leanh::LeanObject,
    mut v_a_4825_: *mut leanh::LeanObject,
    mut v_a_4826_: *mut leanh::LeanObject,
    mut v_a_4827_: *mut leanh::LeanObject,
    mut v_a_4828_: *mut leanh::LeanObject,
    mut v_a_4829_: *mut leanh::LeanObject,
    mut v_a_4830_: *mut leanh::LeanObject,
    mut v_a_4831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4833_ =
        l_Char_reduceIsAlpha___redArg(v_e_4824_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
    return v___x_4833_;
}
pub unsafe fn l_Char_reduceIsAlpha___boxed(
    mut v_e_4834_: *mut leanh::LeanObject,
    mut v_a_4835_: *mut leanh::LeanObject,
    mut v_a_4836_: *mut leanh::LeanObject,
    mut v_a_4837_: *mut leanh::LeanObject,
    mut v_a_4838_: *mut leanh::LeanObject,
    mut v_a_4839_: *mut leanh::LeanObject,
    mut v_a_4840_: *mut leanh::LeanObject,
    mut v_a_4841_: *mut leanh::LeanObject,
    mut v_a_4842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4843_ = l_Char_reduceIsAlpha(
        v_e_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_,
    );
    leanh::lean_dec(v_a_4841_);
    leanh::lean_dec_ref(v_a_4840_);
    leanh::lean_dec(v_a_4839_);
    leanh::lean_dec_ref(v_a_4838_);
    leanh::lean_dec(v_a_4837_);
    leanh::lean_dec_ref(v_a_4836_);
    leanh::lean_dec(v_a_4835_);
    leanh::lean_dec_ref(v_e_4834_);
    return v_res_4843_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4858_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_;
    v___x_4859_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_;
    v___x_4860_ = leanh::lean_alloc_closure(
        l_Char_reduceIsAlpha___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4861_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4858_, v___x_4859_, v___x_4860_);
    return v___x_4861_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13____boxed(
    mut v_a_4862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4863_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_();
    return v_res_4863_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4864_ = leanh::lean_alloc_closure(
        l_Char_reduceIsAlpha___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4865_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4865_, 0, v___x_4864_);
    return v___x_4865_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: u8 = 0;
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_;
    v___x_4868_ = 1;
    v___x_4869_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_);
    v___x_4870_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4867_, v___x_4868_, v___x_4869_);
    return v___x_4870_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15____boxed(
    mut v_a_4871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4872_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_();
    return v_res_4872_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: u8 = 0;
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4874_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_;
    v___x_4875_ = 1;
    v___x_4876_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_);
    v___x_4877_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4874_, v___x_4875_, v___x_4876_);
    return v___x_4877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17____boxed(
    mut v_a_4878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4879_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17_();
    return v_res_4879_;
}
pub unsafe fn l_Char_reduceIsDigit___redArg(
    mut v_e_4884_: *mut leanh::LeanObject,
    mut v_a_4885_: *mut leanh::LeanObject,
    mut v_a_4886_: *mut leanh::LeanObject,
    mut v_a_4887_: *mut leanh::LeanObject,
    mut v_a_4888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: u8 = 0;
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4900_: u8 = 0;
    let mut v___y_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4908_: u8 = 0;
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: u32 = 0;
    let mut v___x_4913_: u32 = 0;
    let mut v___x_4914_: u8 = 0;
    let mut v___x_4915_: u32 = 0;
    let mut v___x_4916_: u32 = 0;
    let mut v___x_4917_: u8 = 0;
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4920_: u8 = 0;
    let mut v_a_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4924_: u8 = 0;
    let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4890_ = l_Char_reduceIsDigit___redArg___closed__1;
                v___x_4891_ = leanh::lean_unsigned_to_nat(1);
                v___x_4892_ = l_Lean_Expr_isAppOfArity(v_e_4884_, v___x_4890_, v___x_4891_);
                if v___x_4892_ == 0 {
                    v___x_4893_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4894_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4894_, 0, v___x_4893_);
                    return v___x_4894_;
                } else {
                    v___x_4895_ = l_Lean_Expr_appArg_x21(v_e_4884_);
                    v___x_4896_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_4895_,
                        v_a_4885_,
                        v_a_4886_,
                        v_a_4887_,
                        v_a_4888_,
                    );
                    if leanh::lean_obj_tag(v___x_4896_) == 0 {
                        v_a_4897_ = leanh::lean_ctor_get(v___x_4896_, 0);
                        v_isSharedCheck_4920_ =
                            (!leanh::lean_is_exclusive(v___x_4896_)) as u8;
                        if v_isSharedCheck_4920_ == 0 {
                            v___x_4899_ = v___x_4896_;
                            v_isShared_4900_ = v_isSharedCheck_4920_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4897_);
                            leanh::lean_dec(v___x_4896_);
                            v___x_4899_ = leanh::lean_box(0);
                            v_isShared_4900_ = v_isSharedCheck_4920_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4921_ = leanh::lean_ctor_get(v___x_4896_, 0);
                        v_isSharedCheck_4928_ =
                            (!leanh::lean_is_exclusive(v___x_4896_)) as u8;
                        if v_isSharedCheck_4928_ == 0 {
                            v___x_4923_ = v___x_4896_;
                            v_isShared_4924_ = v_isSharedCheck_4928_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4921_);
                            leanh::lean_dec(v___x_4896_);
                            v___x_4923_ = leanh::lean_box(0);
                            v_isShared_4924_ = v_isSharedCheck_4928_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4897_) == 1 {
                    v_val_4911_ = leanh::lean_ctor_get(v_a_4897_, 0);
                    leanh::lean_inc(v_val_4911_);
                    leanh::lean_dec_ref_known(v_a_4897_, 1);
                    v___x_4912_ = 48;
                    v___x_4913_ = leanh::lean_unbox_uint32(v_val_4911_);
                    v___x_4914_ = lean_uint32_dec_le(v___x_4912_, v___x_4913_);
                    if v___x_4914_ == 0 {
                        leanh::lean_dec(v_val_4911_);
                        v___y_4908_ = v___x_4914_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4915_ = 57;
                        v___x_4916_ = leanh::lean_unbox_uint32(v_val_4911_);
                        leanh::lean_dec(v_val_4911_);
                        v___x_4917_ = lean_uint32_dec_le(v___x_4916_, v___x_4915_);
                        v___y_4908_ = v___x_4917_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4899_);
                    leanh::lean_dec(v_a_4897_);
                    v___x_4918_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_4919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4919_, 0, v___x_4918_);
                    return v___x_4919_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___y_4902_);
                v___x_4903_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4903_, 0, v___y_4902_);
                if v_isShared_4900_ == 0 {
                    leanh::lean_ctor_set(v___x_4899_, 0, v___x_4903_);
                    v___x_4905_ = v___x_4899_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4906_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
                    v___x_4905_ = v_reuseFailAlloc_4906_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4905_;
            }
            4 => {
                if v___y_4908_ == 0 {
                    v___x_4909_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3_once),
                        _init_l_Char_reduceBoolPred___redArg___closed__3,
                    );
                    v___y_4902_ = v___x_4909_;
                    state = 2;
                    continue;
                } else {
                    v___x_4910_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6_once),
                        _init_l_Char_reduceBoolPred___redArg___closed__6,
                    );
                    v___y_4902_ = v___x_4910_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_4924_ == 0 {
                    v___x_4926_ = v___x_4923_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4927_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
                    v___x_4926_ = v_reuseFailAlloc_4927_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceIsDigit___redArg___boxed(
    mut v_e_4929_: *mut leanh::LeanObject,
    mut v_a_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
    mut v_a_4934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4935_ =
        l_Char_reduceIsDigit___redArg(v_e_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
    leanh::lean_dec(v_a_4933_);
    leanh::lean_dec_ref(v_a_4932_);
    leanh::lean_dec(v_a_4931_);
    leanh::lean_dec_ref(v_a_4930_);
    leanh::lean_dec_ref(v_e_4929_);
    return v_res_4935_;
}
pub unsafe fn l_Char_reduceIsDigit(
    mut v_e_4936_: *mut leanh::LeanObject,
    mut v_a_4937_: *mut leanh::LeanObject,
    mut v_a_4938_: *mut leanh::LeanObject,
    mut v_a_4939_: *mut leanh::LeanObject,
    mut v_a_4940_: *mut leanh::LeanObject,
    mut v_a_4941_: *mut leanh::LeanObject,
    mut v_a_4942_: *mut leanh::LeanObject,
    mut v_a_4943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4945_ =
        l_Char_reduceIsDigit___redArg(v_e_4936_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
    return v___x_4945_;
}
pub unsafe fn l_Char_reduceIsDigit___boxed(
    mut v_e_4946_: *mut leanh::LeanObject,
    mut v_a_4947_: *mut leanh::LeanObject,
    mut v_a_4948_: *mut leanh::LeanObject,
    mut v_a_4949_: *mut leanh::LeanObject,
    mut v_a_4950_: *mut leanh::LeanObject,
    mut v_a_4951_: *mut leanh::LeanObject,
    mut v_a_4952_: *mut leanh::LeanObject,
    mut v_a_4953_: *mut leanh::LeanObject,
    mut v_a_4954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4955_ = l_Char_reduceIsDigit(
        v_e_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_,
    );
    leanh::lean_dec(v_a_4953_);
    leanh::lean_dec_ref(v_a_4952_);
    leanh::lean_dec(v_a_4951_);
    leanh::lean_dec_ref(v_a_4950_);
    leanh::lean_dec(v_a_4949_);
    leanh::lean_dec_ref(v_a_4948_);
    leanh::lean_dec(v_a_4947_);
    leanh::lean_dec_ref(v_e_4946_);
    return v_res_4955_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4970_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_;
    v___x_4971_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_;
    v___x_4972_ = leanh::lean_alloc_closure(
        l_Char_reduceIsDigit___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4973_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4970_, v___x_4971_, v___x_4972_);
    return v___x_4973_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13____boxed(
    mut v_a_4974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4975_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_();
    return v_res_4975_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4976_ = leanh::lean_alloc_closure(
        l_Char_reduceIsDigit___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4977_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4977_, 0, v___x_4976_);
    return v___x_4977_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: u8 = 0;
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4979_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_;
    v___x_4980_ = 1;
    v___x_4981_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_);
    v___x_4982_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_4979_, v___x_4980_, v___x_4981_);
    return v___x_4982_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15____boxed(
    mut v_a_4983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4984_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_();
    return v_res_4984_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_;
    v___x_4987_ = 1;
    v___x_4988_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_);
    v___x_4989_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_4986_, v___x_4987_, v___x_4988_);
    return v___x_4989_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17____boxed(
    mut v_a_4990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4991_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17_();
    return v_res_4991_;
}
pub unsafe fn l_Char_reduceIsAlphaNum___redArg(
    mut v_e_4996_: *mut leanh::LeanObject,
    mut v_a_4997_: *mut leanh::LeanObject,
    mut v_a_4998_: *mut leanh::LeanObject,
    mut v_a_4999_: *mut leanh::LeanObject,
    mut v_a_5000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: u8 = 0;
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v___y_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5022_: u8 = 0;
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5026_: u8 = 0;
    let mut v___x_5027_: u32 = 0;
    let mut v___x_5028_: u32 = 0;
    let mut v___x_5029_: u8 = 0;
    let mut v___x_5030_: u32 = 0;
    let mut v___x_5031_: u32 = 0;
    let mut v___x_5032_: u8 = 0;
    let mut v___x_5034_: u32 = 0;
    let mut v___x_5035_: u32 = 0;
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: u32 = 0;
    let mut v___x_5038_: u32 = 0;
    let mut v___x_5039_: u8 = 0;
    let mut v___x_5040_: u32 = 0;
    let mut v___x_5041_: u32 = 0;
    let mut v___x_5042_: u8 = 0;
    let mut v___x_5043_: u32 = 0;
    let mut v___x_5044_: u32 = 0;
    let mut v___x_5045_: u8 = 0;
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5048_: u8 = 0;
    let mut v_a_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5052_: u8 = 0;
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5002_ = l_Char_reduceIsAlphaNum___redArg___closed__1;
                v___x_5003_ = leanh::lean_unsigned_to_nat(1);
                v___x_5004_ = l_Lean_Expr_isAppOfArity(v_e_4996_, v___x_5002_, v___x_5003_);
                if v___x_5004_ == 0 {
                    v___x_5005_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_5006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5006_, 0, v___x_5005_);
                    return v___x_5006_;
                } else {
                    v___x_5007_ = l_Lean_Expr_appArg_x21(v_e_4996_);
                    v___x_5008_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5007_,
                        v_a_4997_,
                        v_a_4998_,
                        v_a_4999_,
                        v_a_5000_,
                    );
                    if leanh::lean_obj_tag(v___x_5008_) == 0 {
                        v_a_5009_ = leanh::lean_ctor_get(v___x_5008_, 0);
                        v_isSharedCheck_5048_ =
                            (!leanh::lean_is_exclusive(v___x_5008_)) as u8;
                        if v_isSharedCheck_5048_ == 0 {
                            v___x_5011_ = v___x_5008_;
                            v_isShared_5012_ = v_isSharedCheck_5048_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5009_);
                            leanh::lean_dec(v___x_5008_);
                            v___x_5011_ = leanh::lean_box(0);
                            v_isShared_5012_ = v_isSharedCheck_5048_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5049_ = leanh::lean_ctor_get(v___x_5008_, 0);
                        v_isSharedCheck_5056_ =
                            (!leanh::lean_is_exclusive(v___x_5008_)) as u8;
                        if v_isSharedCheck_5056_ == 0 {
                            v___x_5051_ = v___x_5008_;
                            v_isShared_5052_ = v_isSharedCheck_5056_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5049_);
                            leanh::lean_dec(v___x_5008_);
                            v___x_5051_ = leanh::lean_box(0);
                            v_isShared_5052_ = v_isSharedCheck_5056_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5009_) == 1 {
                    v_val_5024_ = leanh::lean_ctor_get(v_a_5009_, 0);
                    leanh::lean_inc(v_val_5024_);
                    leanh::lean_dec_ref_known(v_a_5009_, 1);
                    v___x_5040_ = 65;
                    v___x_5041_ = leanh::lean_unbox_uint32(v_val_5024_);
                    v___x_5042_ = lean_uint32_dec_le(v___x_5040_, v___x_5041_);
                    if v___x_5042_ == 0 {
                        state = 7;
                        continue;
                    } else {
                        v___x_5043_ = 90;
                        v___x_5044_ = leanh::lean_unbox_uint32(v_val_5024_);
                        v___x_5045_ = lean_uint32_dec_le(v___x_5044_, v___x_5043_);
                        if v___x_5045_ == 0 {
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_5024_);
                            v___y_5022_ = v___x_5004_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5011_);
                    leanh::lean_dec(v_a_5009_);
                    v___x_5046_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_5047_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5047_, 0, v___x_5046_);
                    return v___x_5047_;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___y_5014_);
                v___x_5015_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5015_, 0, v___y_5014_);
                if v_isShared_5012_ == 0 {
                    leanh::lean_ctor_set(v___x_5011_, 0, v___x_5015_);
                    v___x_5017_ = v___x_5011_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
                    v___x_5017_ = v_reuseFailAlloc_5018_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5017_;
            }
            4 => {
                v___x_5020_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                    core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6_once),
                    _init_l_Char_reduceBoolPred___redArg___closed__6,
                );
                v___y_5014_ = v___x_5020_;
                state = 2;
                continue;
            }
            5 => {
                if v___y_5022_ == 0 {
                    v___x_5023_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                        core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3_once),
                        _init_l_Char_reduceBoolPred___redArg___closed__3,
                    );
                    v___y_5014_ = v___x_5023_;
                    state = 2;
                    continue;
                } else {
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v___y_5026_ == 0 {
                    v___x_5027_ = 48;
                    v___x_5028_ = leanh::lean_unbox_uint32(v_val_5024_);
                    v___x_5029_ = lean_uint32_dec_le(v___x_5027_, v___x_5028_);
                    if v___x_5029_ == 0 {
                        leanh::lean_dec(v_val_5024_);
                        v___y_5022_ = v___x_5029_;
                        state = 5;
                        continue;
                    } else {
                        v___x_5030_ = 57;
                        v___x_5031_ = leanh::lean_unbox_uint32(v_val_5024_);
                        leanh::lean_dec(v_val_5024_);
                        v___x_5032_ = lean_uint32_dec_le(v___x_5031_, v___x_5030_);
                        v___y_5022_ = v___x_5032_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_val_5024_);
                    state = 4;
                    continue;
                }
            }
            7 => {
                v___x_5034_ = 97;
                v___x_5035_ = leanh::lean_unbox_uint32(v_val_5024_);
                v___x_5036_ = lean_uint32_dec_le(v___x_5034_, v___x_5035_);
                if v___x_5036_ == 0 {
                    v___y_5026_ = v___x_5036_;
                    state = 6;
                    continue;
                } else {
                    v___x_5037_ = 122;
                    v___x_5038_ = leanh::lean_unbox_uint32(v_val_5024_);
                    v___x_5039_ = lean_uint32_dec_le(v___x_5038_, v___x_5037_);
                    v___y_5026_ = v___x_5039_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v_isShared_5052_ == 0 {
                    v___x_5054_ = v___x_5051_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5055_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_a_5049_);
                    v___x_5054_ = v_reuseFailAlloc_5055_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceIsAlphaNum___redArg___boxed(
    mut v_e_5057_: *mut leanh::LeanObject,
    mut v_a_5058_: *mut leanh::LeanObject,
    mut v_a_5059_: *mut leanh::LeanObject,
    mut v_a_5060_: *mut leanh::LeanObject,
    mut v_a_5061_: *mut leanh::LeanObject,
    mut v_a_5062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5063_ =
        l_Char_reduceIsAlphaNum___redArg(v_e_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_);
    leanh::lean_dec(v_a_5061_);
    leanh::lean_dec_ref(v_a_5060_);
    leanh::lean_dec(v_a_5059_);
    leanh::lean_dec_ref(v_a_5058_);
    leanh::lean_dec_ref(v_e_5057_);
    return v_res_5063_;
}
pub unsafe fn l_Char_reduceIsAlphaNum(
    mut v_e_5064_: *mut leanh::LeanObject,
    mut v_a_5065_: *mut leanh::LeanObject,
    mut v_a_5066_: *mut leanh::LeanObject,
    mut v_a_5067_: *mut leanh::LeanObject,
    mut v_a_5068_: *mut leanh::LeanObject,
    mut v_a_5069_: *mut leanh::LeanObject,
    mut v_a_5070_: *mut leanh::LeanObject,
    mut v_a_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5073_ =
        l_Char_reduceIsAlphaNum___redArg(v_e_5064_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
    return v___x_5073_;
}
pub unsafe fn l_Char_reduceIsAlphaNum___boxed(
    mut v_e_5074_: *mut leanh::LeanObject,
    mut v_a_5075_: *mut leanh::LeanObject,
    mut v_a_5076_: *mut leanh::LeanObject,
    mut v_a_5077_: *mut leanh::LeanObject,
    mut v_a_5078_: *mut leanh::LeanObject,
    mut v_a_5079_: *mut leanh::LeanObject,
    mut v_a_5080_: *mut leanh::LeanObject,
    mut v_a_5081_: *mut leanh::LeanObject,
    mut v_a_5082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5083_ = l_Char_reduceIsAlphaNum(
        v_e_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_,
    );
    leanh::lean_dec(v_a_5081_);
    leanh::lean_dec_ref(v_a_5080_);
    leanh::lean_dec(v_a_5079_);
    leanh::lean_dec_ref(v_a_5078_);
    leanh::lean_dec(v_a_5077_);
    leanh::lean_dec_ref(v_a_5076_);
    leanh::lean_dec(v_a_5075_);
    leanh::lean_dec_ref(v_e_5074_);
    return v_res_5083_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5098_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_;
    v___x_5099_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_;
    v___x_5100_ = leanh::lean_alloc_closure(
        l_Char_reduceIsAlphaNum___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5101_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5098_, v___x_5099_, v___x_5100_);
    return v___x_5101_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13____boxed(
    mut v_a_5102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5103_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_();
    return v_res_5103_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5104_ = leanh::lean_alloc_closure(
        l_Char_reduceIsAlphaNum___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5105_, 0, v___x_5104_);
    return v___x_5105_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5107_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_;
    v___x_5108_ = 1;
    v___x_5109_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_);
    v___x_5110_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5107_, v___x_5108_, v___x_5109_);
    return v___x_5110_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15____boxed(
    mut v_a_5111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5112_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_();
    return v_res_5112_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5114_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_;
    v___x_5115_ = 1;
    v___x_5116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_);
    v___x_5117_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5114_, v___x_5115_, v___x_5116_);
    return v___x_5117_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17____boxed(
    mut v_a_5118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5119_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17_();
    return v_res_5119_;
}
pub unsafe fn l_Char_reduceToString___redArg(
    mut v_e_5126_: *mut leanh::LeanObject,
    mut v_a_5127_: *mut leanh::LeanObject,
    mut v_a_5128_: *mut leanh::LeanObject,
    mut v_a_5129_: *mut leanh::LeanObject,
    mut v_a_5130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5142_: u8 = 0;
    let mut v_val_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u32 = 0;
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5157_: u8 = 0;
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5162_: u8 = 0;
    let mut v_a_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5132_ = l_Char_reduceToString___redArg___closed__2;
                v___x_5133_ = leanh::lean_unsigned_to_nat(3);
                v___x_5134_ = l_Lean_Expr_isAppOfArity(v_e_5126_, v___x_5132_, v___x_5133_);
                if v___x_5134_ == 0 {
                    v___x_5135_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_5136_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5136_, 0, v___x_5135_);
                    return v___x_5136_;
                } else {
                    v___x_5137_ = l_Lean_Expr_appArg_x21(v_e_5126_);
                    v___x_5138_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5137_,
                        v_a_5127_,
                        v_a_5128_,
                        v_a_5129_,
                        v_a_5130_,
                    );
                    if leanh::lean_obj_tag(v___x_5138_) == 0 {
                        v_a_5139_ = leanh::lean_ctor_get(v___x_5138_, 0);
                        v_isSharedCheck_5162_ =
                            (!leanh::lean_is_exclusive(v___x_5138_)) as u8;
                        if v_isSharedCheck_5162_ == 0 {
                            v___x_5141_ = v___x_5138_;
                            v_isShared_5142_ = v_isSharedCheck_5162_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5139_);
                            leanh::lean_dec(v___x_5138_);
                            v___x_5141_ = leanh::lean_box(0);
                            v_isShared_5142_ = v_isSharedCheck_5162_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5163_ = leanh::lean_ctor_get(v___x_5138_, 0);
                        v_isSharedCheck_5170_ =
                            (!leanh::lean_is_exclusive(v___x_5138_)) as u8;
                        if v_isSharedCheck_5170_ == 0 {
                            v___x_5165_ = v___x_5138_;
                            v_isShared_5166_ = v_isSharedCheck_5170_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5163_);
                            leanh::lean_dec(v___x_5138_);
                            v___x_5165_ = leanh::lean_box(0);
                            v_isShared_5166_ = v_isSharedCheck_5170_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5139_) == 1 {
                    v_val_5143_ = leanh::lean_ctor_get(v_a_5139_, 0);
                    v_isSharedCheck_5157_ = (!leanh::lean_is_exclusive(v_a_5139_)) as u8;
                    if v_isSharedCheck_5157_ == 0 {
                        v___x_5145_ = v_a_5139_;
                        v_isShared_5146_ = v_isSharedCheck_5157_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5143_);
                        leanh::lean_dec(v_a_5139_);
                        v___x_5145_ = leanh::lean_box(0);
                        v_isShared_5146_ = v_isSharedCheck_5157_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5139_);
                    v___x_5158_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_5142_ == 0 {
                        leanh::lean_ctor_set(v___x_5141_, 0, v___x_5158_);
                        v___x_5160_ = v___x_5141_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5161_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 0, v___x_5158_);
                        v___x_5160_ = v_reuseFailAlloc_5161_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5147_ = l_Char_reduceToString___redArg___closed__3;
                v___x_5148_ = leanh::lean_unbox_uint32(v_val_5143_);
                leanh::lean_dec(v_val_5143_);
                v___x_5149_ = lean_string_push(v___x_5147_, v___x_5148_);
                v___x_5150_ = l_Lean_mkStrLit(v___x_5149_);
                if v_isShared_5146_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5145_, 0);
                    leanh::lean_ctor_set(v___x_5145_, 0, v___x_5150_);
                    v___x_5152_ = v___x_5145_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5150_);
                    v___x_5152_ = v_reuseFailAlloc_5156_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5142_ == 0 {
                    leanh::lean_ctor_set(v___x_5141_, 0, v___x_5152_);
                    v___x_5154_ = v___x_5141_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5155_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
                    v___x_5154_ = v_reuseFailAlloc_5155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5154_;
            }
            5 => {
                return v___x_5160_;
            }
            6 => {
                if v_isShared_5166_ == 0 {
                    v___x_5168_ = v___x_5165_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
                    v___x_5168_ = v_reuseFailAlloc_5169_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceToString___redArg___boxed(
    mut v_e_5171_: *mut leanh::LeanObject,
    mut v_a_5172_: *mut leanh::LeanObject,
    mut v_a_5173_: *mut leanh::LeanObject,
    mut v_a_5174_: *mut leanh::LeanObject,
    mut v_a_5175_: *mut leanh::LeanObject,
    mut v_a_5176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5177_ =
        l_Char_reduceToString___redArg(v_e_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_);
    leanh::lean_dec(v_a_5175_);
    leanh::lean_dec_ref(v_a_5174_);
    leanh::lean_dec(v_a_5173_);
    leanh::lean_dec_ref(v_a_5172_);
    leanh::lean_dec_ref(v_e_5171_);
    return v_res_5177_;
}
pub unsafe fn l_Char_reduceToString(
    mut v_e_5178_: *mut leanh::LeanObject,
    mut v_a_5179_: *mut leanh::LeanObject,
    mut v_a_5180_: *mut leanh::LeanObject,
    mut v_a_5181_: *mut leanh::LeanObject,
    mut v_a_5182_: *mut leanh::LeanObject,
    mut v_a_5183_: *mut leanh::LeanObject,
    mut v_a_5184_: *mut leanh::LeanObject,
    mut v_a_5185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5187_ =
        l_Char_reduceToString___redArg(v_e_5178_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_);
    return v___x_5187_;
}
pub unsafe fn l_Char_reduceToString___boxed(
    mut v_e_5188_: *mut leanh::LeanObject,
    mut v_a_5189_: *mut leanh::LeanObject,
    mut v_a_5190_: *mut leanh::LeanObject,
    mut v_a_5191_: *mut leanh::LeanObject,
    mut v_a_5192_: *mut leanh::LeanObject,
    mut v_a_5193_: *mut leanh::LeanObject,
    mut v_a_5194_: *mut leanh::LeanObject,
    mut v_a_5195_: *mut leanh::LeanObject,
    mut v_a_5196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5197_ = l_Char_reduceToString(
        v_e_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_,
    );
    leanh::lean_dec(v_a_5195_);
    leanh::lean_dec_ref(v_a_5194_);
    leanh::lean_dec(v_a_5193_);
    leanh::lean_dec_ref(v_a_5192_);
    leanh::lean_dec(v_a_5191_);
    leanh::lean_dec_ref(v_a_5190_);
    leanh::lean_dec(v_a_5189_);
    leanh::lean_dec_ref(v_e_5188_);
    return v_res_5197_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_()
-> *mut leanh::LeanObject {
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5220_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_;
    v___x_5221_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_;
    v___x_5222_ = leanh::lean_alloc_closure(
        l_Char_reduceToString___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5223_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5220_, v___x_5221_, v___x_5222_);
    return v___x_5223_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16____boxed(
    mut v_a_5224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5225_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_();
    return v_res_5225_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_()
-> *mut leanh::LeanObject {
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5226_ = leanh::lean_alloc_closure(
        l_Char_reduceToString___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5227_, 0, v___x_5226_);
    return v___x_5227_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_()
-> *mut leanh::LeanObject {
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: u8 = 0;
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5229_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_;
    v___x_5230_ = 1;
    v___x_5231_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_);
    v___x_5232_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5229_, v___x_5230_, v___x_5231_);
    return v___x_5232_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18____boxed(
    mut v_a_5233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5234_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_();
    return v_res_5234_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: u8 = 0;
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5236_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_;
    v___x_5237_ = 1;
    v___x_5238_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_);
    v___x_5239_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5236_, v___x_5237_, v___x_5238_);
    return v___x_5239_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20____boxed(
    mut v_a_5240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5241_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20_();
    return v_res_5241_;
}
pub unsafe fn _init_l_Char_reduceVal___redArg___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5250_ = leanh::lean_unsigned_to_nat(0);
    v___x_5251_ = l_Lean_Level_ofNat(v___x_5250_);
    return v___x_5251_;
}
pub unsafe fn _init_l_Char_reduceVal___redArg___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5252_ = leanh::lean_box(0);
    v___x_5253_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__4_once),
        _init_l_Char_reduceVal___redArg___closed__4,
    );
    v___x_5254_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5254_, 0, v___x_5253_);
    leanh::lean_ctor_set(v___x_5254_, 1, v___x_5252_);
    return v___x_5254_;
}
pub unsafe fn _init_l_Char_reduceVal___redArg___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5255_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__5_once),
        _init_l_Char_reduceVal___redArg___closed__5,
    );
    v___x_5256_ = l_Char_reduceVal___redArg___closed__3;
    v___x_5257_ = l_Lean_Expr_const___override(v___x_5256_, v___x_5255_);
    return v___x_5257_;
}
pub unsafe fn _init_l_Char_reduceVal___redArg___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5261_ = leanh::lean_box(0);
    v___x_5262_ = l_Char_reduceVal___redArg___closed__8;
    v___x_5263_ = l_Lean_mkConst(v___x_5262_, v___x_5261_);
    return v___x_5263_;
}
pub unsafe fn _init_l_Char_reduceVal___redArg___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5268_ = leanh::lean_box(0);
    v___x_5269_ = l_Char_reduceVal___redArg___closed__11;
    v___x_5270_ = l_Lean_Expr_const___override(v___x_5269_, v___x_5268_);
    return v___x_5270_;
}
pub unsafe fn l_Char_reduceVal___redArg(
    mut v_e_5271_: *mut leanh::LeanObject,
    mut v_a_5272_: *mut leanh::LeanObject,
    mut v_a_5273_: *mut leanh::LeanObject,
    mut v_a_5274_: *mut leanh::LeanObject,
    mut v_a_5275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5281_: u8 = 0;
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: u8 = 0;
    let mut v_arg_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: u8 = 0;
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5297_: u8 = 0;
    let mut v_val_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5302_: u32 = 0;
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5321_: u8 = 0;
    let mut v_a_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5325_: u8 = 0;
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5329_: u8 = 0;
    let mut v_isSharedCheck_5330_: u8 = 0;
    let mut v_a_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5334_: u8 = 0;
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5277_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5271_, v_a_5273_);
                if leanh::lean_obj_tag(v___x_5277_) == 0 {
                    v_a_5278_ = leanh::lean_ctor_get(v___x_5277_, 0);
                    v_isSharedCheck_5330_ = (!leanh::lean_is_exclusive(v___x_5277_)) as u8;
                    if v_isSharedCheck_5330_ == 0 {
                        v___x_5280_ = v___x_5277_;
                        v_isShared_5281_ = v_isSharedCheck_5330_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5278_);
                        leanh::lean_dec(v___x_5277_);
                        v___x_5280_ = leanh::lean_box(0);
                        v_isShared_5281_ = v_isSharedCheck_5330_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5331_ = leanh::lean_ctor_get(v___x_5277_, 0);
                    v_isSharedCheck_5338_ = (!leanh::lean_is_exclusive(v___x_5277_)) as u8;
                    if v_isSharedCheck_5338_ == 0 {
                        v___x_5333_ = v___x_5277_;
                        v_isShared_5334_ = v_isSharedCheck_5338_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5331_);
                        leanh::lean_dec(v___x_5277_);
                        v___x_5333_ = leanh::lean_box(0);
                        v_isShared_5334_ = v_isSharedCheck_5338_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5287_ = l_Lean_Expr_cleanupAnnotations(v_a_5278_);
                v___x_5288_ = l_Lean_Expr_isApp(v___x_5287_);
                if v___x_5288_ == 0 {
                    leanh::lean_dec_ref(v___x_5287_);
                    state = 2;
                    continue;
                } else {
                    v_arg_5289_ = leanh::lean_ctor_get(v___x_5287_, 1);
                    leanh::lean_inc_ref(v_arg_5289_);
                    v___x_5290_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5287_);
                    v___x_5291_ = l_Char_reduceVal___redArg___closed__1;
                    v___x_5292_ = l_Lean_Expr_isConstOf(v___x_5290_, v___x_5291_);
                    leanh::lean_dec_ref(v___x_5290_);
                    if v___x_5292_ == 0 {
                        leanh::lean_dec_ref(v_arg_5289_);
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_5280_);
                        v___x_5293_ = l_Lean_Meta_getCharValue_x3f(
                            v_arg_5289_,
                            v_a_5272_,
                            v_a_5273_,
                            v_a_5274_,
                            v_a_5275_,
                        );
                        if leanh::lean_obj_tag(v___x_5293_) == 0 {
                            v_a_5294_ = leanh::lean_ctor_get(v___x_5293_, 0);
                            v_isSharedCheck_5321_ =
                                (!leanh::lean_is_exclusive(v___x_5293_)) as u8;
                            if v_isSharedCheck_5321_ == 0 {
                                v___x_5296_ = v___x_5293_;
                                v_isShared_5297_ = v_isSharedCheck_5321_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5294_);
                                leanh::lean_dec(v___x_5293_);
                                v___x_5296_ = leanh::lean_box(0);
                                v_isShared_5297_ = v_isSharedCheck_5321_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_5322_ = leanh::lean_ctor_get(v___x_5293_, 0);
                            v_isSharedCheck_5329_ =
                                (!leanh::lean_is_exclusive(v___x_5293_)) as u8;
                            if v_isSharedCheck_5329_ == 0 {
                                v___x_5324_ = v___x_5293_;
                                v_isShared_5325_ = v_isSharedCheck_5329_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5322_);
                                leanh::lean_dec(v___x_5293_);
                                v___x_5324_ = leanh::lean_box(0);
                                v_isShared_5325_ = v_isSharedCheck_5329_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_5283_ = l_Char_reduceUnary___redArg___closed__0;
                if v_isShared_5281_ == 0 {
                    leanh::lean_ctor_set(v___x_5280_, 0, v___x_5283_);
                    v___x_5285_ = v___x_5280_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5286_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5283_);
                    v___x_5285_ = v_reuseFailAlloc_5286_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5285_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_5294_) == 1 {
                    v_val_5298_ = leanh::lean_ctor_get(v_a_5294_, 0);
                    v_isSharedCheck_5316_ = (!leanh::lean_is_exclusive(v_a_5294_)) as u8;
                    if v_isSharedCheck_5316_ == 0 {
                        v___x_5300_ = v_a_5294_;
                        v_isShared_5301_ = v_isSharedCheck_5316_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5298_);
                        leanh::lean_dec(v_a_5294_);
                        v___x_5300_ = leanh::lean_box(0);
                        v_isShared_5301_ = v_isSharedCheck_5316_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5294_);
                    v___x_5317_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_5297_ == 0 {
                        leanh::lean_ctor_set(v___x_5296_, 0, v___x_5317_);
                        v___x_5319_ = v___x_5296_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5320_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5320_, 0, v___x_5317_);
                        v___x_5319_ = v_reuseFailAlloc_5320_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5302_ = leanh::lean_unbox_uint32(v_val_5298_);
                leanh::lean_dec(v_val_5298_);
                v___x_5303_ = lean_uint32_to_nat(v___x_5302_);
                v_r_5304_ = l_Lean_mkRawNatLit(v___x_5303_);
                v___x_5305_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__6),
                    core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__6_once),
                    _init_l_Char_reduceVal___redArg___closed__6,
                );
                v___x_5306_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__9),
                    core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__9_once),
                    _init_l_Char_reduceVal___redArg___closed__9,
                );
                v___x_5307_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__12),
                    core::ptr::addr_of_mut!(l_Char_reduceVal___redArg___closed__12_once),
                    _init_l_Char_reduceVal___redArg___closed__12,
                );
                leanh::lean_inc_ref(v_r_5304_);
                v___x_5308_ = l_Lean_Expr_app___override(v___x_5307_, v_r_5304_);
                v___x_5309_ = l_Lean_mkApp3(v___x_5305_, v___x_5306_, v_r_5304_, v___x_5308_);
                if v_isShared_5301_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5300_, 0);
                    leanh::lean_ctor_set(v___x_5300_, 0, v___x_5309_);
                    v___x_5311_ = v___x_5300_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5309_);
                    v___x_5311_ = v_reuseFailAlloc_5315_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5297_ == 0 {
                    leanh::lean_ctor_set(v___x_5296_, 0, v___x_5311_);
                    v___x_5313_ = v___x_5296_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5314_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5311_);
                    v___x_5313_ = v_reuseFailAlloc_5314_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5313_;
            }
            8 => {
                return v___x_5319_;
            }
            9 => {
                if v_isShared_5325_ == 0 {
                    v___x_5327_ = v___x_5324_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
                    v___x_5327_ = v_reuseFailAlloc_5328_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5327_;
            }
            11 => {
                if v_isShared_5334_ == 0 {
                    v___x_5336_ = v___x_5333_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_a_5331_);
                    v___x_5336_ = v_reuseFailAlloc_5337_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceVal___redArg___boxed(
    mut v_e_5339_: *mut leanh::LeanObject,
    mut v_a_5340_: *mut leanh::LeanObject,
    mut v_a_5341_: *mut leanh::LeanObject,
    mut v_a_5342_: *mut leanh::LeanObject,
    mut v_a_5343_: *mut leanh::LeanObject,
    mut v_a_5344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5345_ = l_Char_reduceVal___redArg(v_e_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_);
    leanh::lean_dec(v_a_5343_);
    leanh::lean_dec_ref(v_a_5342_);
    leanh::lean_dec(v_a_5341_);
    leanh::lean_dec_ref(v_a_5340_);
    return v_res_5345_;
}
pub unsafe fn l_Char_reduceVal(
    mut v_e_5346_: *mut leanh::LeanObject,
    mut v_a_5347_: *mut leanh::LeanObject,
    mut v_a_5348_: *mut leanh::LeanObject,
    mut v_a_5349_: *mut leanh::LeanObject,
    mut v_a_5350_: *mut leanh::LeanObject,
    mut v_a_5351_: *mut leanh::LeanObject,
    mut v_a_5352_: *mut leanh::LeanObject,
    mut v_a_5353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5355_ = l_Char_reduceVal___redArg(v_e_5346_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_);
    return v___x_5355_;
}
pub unsafe fn l_Char_reduceVal___boxed(
    mut v_e_5356_: *mut leanh::LeanObject,
    mut v_a_5357_: *mut leanh::LeanObject,
    mut v_a_5358_: *mut leanh::LeanObject,
    mut v_a_5359_: *mut leanh::LeanObject,
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_a_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
    mut v_a_5364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5365_ = l_Char_reduceVal(
        v_e_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_,
    );
    leanh::lean_dec(v_a_5363_);
    leanh::lean_dec_ref(v_a_5362_);
    leanh::lean_dec(v_a_5361_);
    leanh::lean_dec_ref(v_a_5360_);
    leanh::lean_dec(v_a_5359_);
    leanh::lean_dec_ref(v_a_5358_);
    leanh::lean_dec(v_a_5357_);
    return v_res_5365_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5380_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_;
    v___x_5381_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_;
    v___x_5382_ =
        leanh::lean_alloc_closure(l_Char_reduceVal___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5383_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_5380_, v___x_5381_, v___x_5382_);
    return v___x_5383_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13____boxed(
    mut v_a_5384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5385_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_();
    return v_res_5385_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5386_ =
        leanh::lean_alloc_closure(l_Char_reduceVal___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5387_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5387_, 0, v___x_5386_);
    return v___x_5387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: u8 = 0;
    let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5389_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_;
    v___x_5390_ = 1;
    v___x_5391_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_);
    v___x_5392_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5389_, v___x_5390_, v___x_5391_);
    return v___x_5392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15____boxed(
    mut v_a_5393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5394_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_();
    return v_res_5394_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: u8 = 0;
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5396_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_;
    v___x_5397_ = 1;
    v___x_5398_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_);
    v___x_5399_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5396_, v___x_5397_, v___x_5398_);
    return v___x_5399_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17____boxed(
    mut v_a_5400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5401_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17_();
    return v_res_5401_;
}
pub unsafe fn l_Char_reduceLT___redArg(
    mut v_e_5407_: *mut leanh::LeanObject,
    mut v_a_5408_: *mut leanh::LeanObject,
    mut v_a_5409_: *mut leanh::LeanObject,
    mut v_a_5410_: *mut leanh::LeanObject,
    mut v_a_5411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: u8 = 0;
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v_val_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5431_: u8 = 0;
    let mut v_val_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: u32 = 0;
    let mut v___x_5434_: u32 = 0;
    let mut v___x_5435_: u8 = 0;
    let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5441_: u8 = 0;
    let mut v_a_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5445_: u8 = 0;
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5449_: u8 = 0;
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut v_a_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5458_: u8 = 0;
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5413_ = l_Char_reduceLT___redArg___closed__2;
                v___x_5414_ = leanh::lean_unsigned_to_nat(4);
                v___x_5415_ = l_Lean_Expr_isAppOfArity(v_e_5407_, v___x_5413_, v___x_5414_);
                if v___x_5415_ == 0 {
                    leanh::lean_dec_ref(v_e_5407_);
                    v___x_5416_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_5417_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5417_, 0, v___x_5416_);
                    return v___x_5417_;
                } else {
                    v___x_5418_ = l_Lean_Expr_appFn_x21(v_e_5407_);
                    v___x_5419_ = l_Lean_Expr_appArg_x21(v___x_5418_);
                    leanh::lean_dec_ref(v___x_5418_);
                    v___x_5420_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5419_,
                        v_a_5408_,
                        v_a_5409_,
                        v_a_5410_,
                        v_a_5411_,
                    );
                    if leanh::lean_obj_tag(v___x_5420_) == 0 {
                        v_a_5421_ = leanh::lean_ctor_get(v___x_5420_, 0);
                        v_isSharedCheck_5454_ =
                            (!leanh::lean_is_exclusive(v___x_5420_)) as u8;
                        if v_isSharedCheck_5454_ == 0 {
                            v___x_5423_ = v___x_5420_;
                            v_isShared_5424_ = v_isSharedCheck_5454_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5421_);
                            leanh::lean_dec(v___x_5420_);
                            v___x_5423_ = leanh::lean_box(0);
                            v_isShared_5424_ = v_isSharedCheck_5454_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_5407_);
                        v_a_5455_ = leanh::lean_ctor_get(v___x_5420_, 0);
                        v_isSharedCheck_5462_ =
                            (!leanh::lean_is_exclusive(v___x_5420_)) as u8;
                        if v_isSharedCheck_5462_ == 0 {
                            v___x_5457_ = v___x_5420_;
                            v_isShared_5458_ = v_isSharedCheck_5462_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5455_);
                            leanh::lean_dec(v___x_5420_);
                            v___x_5457_ = leanh::lean_box(0);
                            v_isShared_5458_ = v_isSharedCheck_5462_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5421_) == 1 {
                    leanh::lean_del_object(v___x_5423_);
                    v_val_5425_ = leanh::lean_ctor_get(v_a_5421_, 0);
                    leanh::lean_inc(v_val_5425_);
                    leanh::lean_dec_ref_known(v_a_5421_, 1);
                    v___x_5426_ = l_Lean_Expr_appArg_x21(v_e_5407_);
                    v___x_5427_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5426_,
                        v_a_5408_,
                        v_a_5409_,
                        v_a_5410_,
                        v_a_5411_,
                    );
                    if leanh::lean_obj_tag(v___x_5427_) == 0 {
                        v_a_5428_ = leanh::lean_ctor_get(v___x_5427_, 0);
                        v_isSharedCheck_5441_ =
                            (!leanh::lean_is_exclusive(v___x_5427_)) as u8;
                        if v_isSharedCheck_5441_ == 0 {
                            v___x_5430_ = v___x_5427_;
                            v_isShared_5431_ = v_isSharedCheck_5441_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5428_);
                            leanh::lean_dec(v___x_5427_);
                            v___x_5430_ = leanh::lean_box(0);
                            v_isShared_5431_ = v_isSharedCheck_5441_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5425_);
                        leanh::lean_dec_ref(v_e_5407_);
                        v_a_5442_ = leanh::lean_ctor_get(v___x_5427_, 0);
                        v_isSharedCheck_5449_ =
                            (!leanh::lean_is_exclusive(v___x_5427_)) as u8;
                        if v_isSharedCheck_5449_ == 0 {
                            v___x_5444_ = v___x_5427_;
                            v_isShared_5445_ = v_isSharedCheck_5449_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5442_);
                            leanh::lean_dec(v___x_5427_);
                            v___x_5444_ = leanh::lean_box(0);
                            v_isShared_5445_ = v_isSharedCheck_5449_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5421_);
                    leanh::lean_dec_ref(v_e_5407_);
                    v___x_5450_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5424_ == 0 {
                        leanh::lean_ctor_set(v___x_5423_, 0, v___x_5450_);
                        v___x_5452_ = v___x_5423_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5453_, 0, v___x_5450_);
                        v___x_5452_ = v_reuseFailAlloc_5453_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5428_) == 1 {
                    leanh::lean_del_object(v___x_5430_);
                    v_val_5432_ = leanh::lean_ctor_get(v_a_5428_, 0);
                    leanh::lean_inc(v_val_5432_);
                    leanh::lean_dec_ref_known(v_a_5428_, 1);
                    v___x_5433_ = leanh::lean_unbox_uint32(v_val_5425_);
                    leanh::lean_dec(v_val_5425_);
                    v___x_5434_ = leanh::lean_unbox_uint32(v_val_5432_);
                    leanh::lean_dec(v_val_5432_);
                    v___x_5435_ = lean_uint32_dec_lt(v___x_5433_, v___x_5434_);
                    v___x_5436_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_5407_,
                        v___x_5435_,
                        v_a_5408_,
                        v_a_5409_,
                        v_a_5410_,
                        v_a_5411_,
                    );
                    return v___x_5436_;
                } else {
                    leanh::lean_dec(v_a_5428_);
                    leanh::lean_dec(v_val_5425_);
                    leanh::lean_dec_ref(v_e_5407_);
                    v___x_5437_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5431_ == 0 {
                        leanh::lean_ctor_set(v___x_5430_, 0, v___x_5437_);
                        v___x_5439_ = v___x_5430_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5440_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5437_);
                        v___x_5439_ = v_reuseFailAlloc_5440_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5439_;
            }
            4 => {
                if v_isShared_5445_ == 0 {
                    v___x_5447_ = v___x_5444_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_a_5442_);
                    v___x_5447_ = v_reuseFailAlloc_5448_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5447_;
            }
            6 => {
                return v___x_5452_;
            }
            7 => {
                if v_isShared_5458_ == 0 {
                    v___x_5460_ = v___x_5457_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
                    v___x_5460_ = v_reuseFailAlloc_5461_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceLT___redArg___boxed(
    mut v_e_5463_: *mut leanh::LeanObject,
    mut v_a_5464_: *mut leanh::LeanObject,
    mut v_a_5465_: *mut leanh::LeanObject,
    mut v_a_5466_: *mut leanh::LeanObject,
    mut v_a_5467_: *mut leanh::LeanObject,
    mut v_a_5468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5469_ = l_Char_reduceLT___redArg(v_e_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_);
    leanh::lean_dec(v_a_5467_);
    leanh::lean_dec_ref(v_a_5466_);
    leanh::lean_dec(v_a_5465_);
    leanh::lean_dec_ref(v_a_5464_);
    return v_res_5469_;
}
pub unsafe fn l_Char_reduceLT(
    mut v_e_5470_: *mut leanh::LeanObject,
    mut v_a_5471_: *mut leanh::LeanObject,
    mut v_a_5472_: *mut leanh::LeanObject,
    mut v_a_5473_: *mut leanh::LeanObject,
    mut v_a_5474_: *mut leanh::LeanObject,
    mut v_a_5475_: *mut leanh::LeanObject,
    mut v_a_5476_: *mut leanh::LeanObject,
    mut v_a_5477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5479_ = l_Char_reduceLT___redArg(v_e_5470_, v_a_5474_, v_a_5475_, v_a_5476_, v_a_5477_);
    return v___x_5479_;
}
pub unsafe fn l_Char_reduceLT___boxed(
    mut v_e_5480_: *mut leanh::LeanObject,
    mut v_a_5481_: *mut leanh::LeanObject,
    mut v_a_5482_: *mut leanh::LeanObject,
    mut v_a_5483_: *mut leanh::LeanObject,
    mut v_a_5484_: *mut leanh::LeanObject,
    mut v_a_5485_: *mut leanh::LeanObject,
    mut v_a_5486_: *mut leanh::LeanObject,
    mut v_a_5487_: *mut leanh::LeanObject,
    mut v_a_5488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5489_ = l_Char_reduceLT(
        v_e_5480_, v_a_5481_, v_a_5482_, v_a_5483_, v_a_5484_, v_a_5485_, v_a_5486_, v_a_5487_,
    );
    leanh::lean_dec(v_a_5487_);
    leanh::lean_dec_ref(v_a_5486_);
    leanh::lean_dec(v_a_5485_);
    leanh::lean_dec_ref(v_a_5484_);
    leanh::lean_dec(v_a_5483_);
    leanh::lean_dec_ref(v_a_5482_);
    leanh::lean_dec(v_a_5481_);
    return v_res_5489_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5508_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_;
    v___x_5509_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_;
    v___x_5510_ =
        leanh::lean_alloc_closure(l_Char_reduceLT___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5511_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5508_, v___x_5509_, v___x_5510_);
    return v___x_5511_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20____boxed(
    mut v_a_5512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5513_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_();
    return v_res_5513_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5514_ =
        leanh::lean_alloc_closure(l_Char_reduceLT___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5515_, 0, v___x_5514_);
    return v___x_5515_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: u8 = 0;
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5517_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_;
    v___x_5518_ = 1;
    v___x_5519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_);
    v___x_5520_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5517_, v___x_5518_, v___x_5519_);
    return v___x_5520_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22____boxed(
    mut v_a_5521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5522_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_();
    return v_res_5522_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: u8 = 0;
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5524_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_;
    v___x_5525_ = 1;
    v___x_5526_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_);
    v___x_5527_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5524_, v___x_5525_, v___x_5526_);
    return v___x_5527_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24____boxed(
    mut v_a_5528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5529_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24_();
    return v_res_5529_;
}
pub unsafe fn l_Char_reduceLE___redArg(
    mut v_e_5535_: *mut leanh::LeanObject,
    mut v_a_5536_: *mut leanh::LeanObject,
    mut v_a_5537_: *mut leanh::LeanObject,
    mut v_a_5538_: *mut leanh::LeanObject,
    mut v_a_5539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: u8 = 0;
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5552_: u8 = 0;
    let mut v_val_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5559_: u8 = 0;
    let mut v_val_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: u32 = 0;
    let mut v___x_5562_: u32 = 0;
    let mut v___x_5563_: u8 = 0;
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5569_: u8 = 0;
    let mut v_a_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5573_: u8 = 0;
    let mut v___x_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5577_: u8 = 0;
    let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5582_: u8 = 0;
    let mut v_a_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5586_: u8 = 0;
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5541_ = l_Char_reduceLE___redArg___closed__2;
                v___x_5542_ = leanh::lean_unsigned_to_nat(4);
                v___x_5543_ = l_Lean_Expr_isAppOfArity(v_e_5535_, v___x_5541_, v___x_5542_);
                if v___x_5543_ == 0 {
                    leanh::lean_dec_ref(v_e_5535_);
                    v___x_5544_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_5545_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5545_, 0, v___x_5544_);
                    return v___x_5545_;
                } else {
                    v___x_5546_ = l_Lean_Expr_appFn_x21(v_e_5535_);
                    v___x_5547_ = l_Lean_Expr_appArg_x21(v___x_5546_);
                    leanh::lean_dec_ref(v___x_5546_);
                    v___x_5548_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5547_,
                        v_a_5536_,
                        v_a_5537_,
                        v_a_5538_,
                        v_a_5539_,
                    );
                    if leanh::lean_obj_tag(v___x_5548_) == 0 {
                        v_a_5549_ = leanh::lean_ctor_get(v___x_5548_, 0);
                        v_isSharedCheck_5582_ =
                            (!leanh::lean_is_exclusive(v___x_5548_)) as u8;
                        if v_isSharedCheck_5582_ == 0 {
                            v___x_5551_ = v___x_5548_;
                            v_isShared_5552_ = v_isSharedCheck_5582_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5549_);
                            leanh::lean_dec(v___x_5548_);
                            v___x_5551_ = leanh::lean_box(0);
                            v_isShared_5552_ = v_isSharedCheck_5582_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_5535_);
                        v_a_5583_ = leanh::lean_ctor_get(v___x_5548_, 0);
                        v_isSharedCheck_5590_ =
                            (!leanh::lean_is_exclusive(v___x_5548_)) as u8;
                        if v_isSharedCheck_5590_ == 0 {
                            v___x_5585_ = v___x_5548_;
                            v_isShared_5586_ = v_isSharedCheck_5590_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5583_);
                            leanh::lean_dec(v___x_5548_);
                            v___x_5585_ = leanh::lean_box(0);
                            v_isShared_5586_ = v_isSharedCheck_5590_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5549_) == 1 {
                    leanh::lean_del_object(v___x_5551_);
                    v_val_5553_ = leanh::lean_ctor_get(v_a_5549_, 0);
                    leanh::lean_inc(v_val_5553_);
                    leanh::lean_dec_ref_known(v_a_5549_, 1);
                    v___x_5554_ = l_Lean_Expr_appArg_x21(v_e_5535_);
                    v___x_5555_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5554_,
                        v_a_5536_,
                        v_a_5537_,
                        v_a_5538_,
                        v_a_5539_,
                    );
                    if leanh::lean_obj_tag(v___x_5555_) == 0 {
                        v_a_5556_ = leanh::lean_ctor_get(v___x_5555_, 0);
                        v_isSharedCheck_5569_ =
                            (!leanh::lean_is_exclusive(v___x_5555_)) as u8;
                        if v_isSharedCheck_5569_ == 0 {
                            v___x_5558_ = v___x_5555_;
                            v_isShared_5559_ = v_isSharedCheck_5569_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5556_);
                            leanh::lean_dec(v___x_5555_);
                            v___x_5558_ = leanh::lean_box(0);
                            v_isShared_5559_ = v_isSharedCheck_5569_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5553_);
                        leanh::lean_dec_ref(v_e_5535_);
                        v_a_5570_ = leanh::lean_ctor_get(v___x_5555_, 0);
                        v_isSharedCheck_5577_ =
                            (!leanh::lean_is_exclusive(v___x_5555_)) as u8;
                        if v_isSharedCheck_5577_ == 0 {
                            v___x_5572_ = v___x_5555_;
                            v_isShared_5573_ = v_isSharedCheck_5577_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5570_);
                            leanh::lean_dec(v___x_5555_);
                            v___x_5572_ = leanh::lean_box(0);
                            v_isShared_5573_ = v_isSharedCheck_5577_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5549_);
                    leanh::lean_dec_ref(v_e_5535_);
                    v___x_5578_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5552_ == 0 {
                        leanh::lean_ctor_set(v___x_5551_, 0, v___x_5578_);
                        v___x_5580_ = v___x_5551_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5581_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5578_);
                        v___x_5580_ = v_reuseFailAlloc_5581_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5556_) == 1 {
                    leanh::lean_del_object(v___x_5558_);
                    v_val_5560_ = leanh::lean_ctor_get(v_a_5556_, 0);
                    leanh::lean_inc(v_val_5560_);
                    leanh::lean_dec_ref_known(v_a_5556_, 1);
                    v___x_5561_ = leanh::lean_unbox_uint32(v_val_5553_);
                    leanh::lean_dec(v_val_5553_);
                    v___x_5562_ = leanh::lean_unbox_uint32(v_val_5560_);
                    leanh::lean_dec(v_val_5560_);
                    v___x_5563_ = lean_uint32_dec_le(v___x_5561_, v___x_5562_);
                    v___x_5564_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_5535_,
                        v___x_5563_,
                        v_a_5536_,
                        v_a_5537_,
                        v_a_5538_,
                        v_a_5539_,
                    );
                    return v___x_5564_;
                } else {
                    leanh::lean_dec(v_a_5556_);
                    leanh::lean_dec(v_val_5553_);
                    leanh::lean_dec_ref(v_e_5535_);
                    v___x_5565_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5559_ == 0 {
                        leanh::lean_ctor_set(v___x_5558_, 0, v___x_5565_);
                        v___x_5567_ = v___x_5558_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5565_);
                        v___x_5567_ = v_reuseFailAlloc_5568_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5567_;
            }
            4 => {
                if v_isShared_5573_ == 0 {
                    v___x_5575_ = v___x_5572_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5576_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5576_, 0, v_a_5570_);
                    v___x_5575_ = v_reuseFailAlloc_5576_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5575_;
            }
            6 => {
                return v___x_5580_;
            }
            7 => {
                if v_isShared_5586_ == 0 {
                    v___x_5588_ = v___x_5585_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5589_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
                    v___x_5588_ = v_reuseFailAlloc_5589_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceLE___redArg___boxed(
    mut v_e_5591_: *mut leanh::LeanObject,
    mut v_a_5592_: *mut leanh::LeanObject,
    mut v_a_5593_: *mut leanh::LeanObject,
    mut v_a_5594_: *mut leanh::LeanObject,
    mut v_a_5595_: *mut leanh::LeanObject,
    mut v_a_5596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5597_ = l_Char_reduceLE___redArg(v_e_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_);
    leanh::lean_dec(v_a_5595_);
    leanh::lean_dec_ref(v_a_5594_);
    leanh::lean_dec(v_a_5593_);
    leanh::lean_dec_ref(v_a_5592_);
    return v_res_5597_;
}
pub unsafe fn l_Char_reduceLE(
    mut v_e_5598_: *mut leanh::LeanObject,
    mut v_a_5599_: *mut leanh::LeanObject,
    mut v_a_5600_: *mut leanh::LeanObject,
    mut v_a_5601_: *mut leanh::LeanObject,
    mut v_a_5602_: *mut leanh::LeanObject,
    mut v_a_5603_: *mut leanh::LeanObject,
    mut v_a_5604_: *mut leanh::LeanObject,
    mut v_a_5605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5607_ = l_Char_reduceLE___redArg(v_e_5598_, v_a_5602_, v_a_5603_, v_a_5604_, v_a_5605_);
    return v___x_5607_;
}
pub unsafe fn l_Char_reduceLE___boxed(
    mut v_e_5608_: *mut leanh::LeanObject,
    mut v_a_5609_: *mut leanh::LeanObject,
    mut v_a_5610_: *mut leanh::LeanObject,
    mut v_a_5611_: *mut leanh::LeanObject,
    mut v_a_5612_: *mut leanh::LeanObject,
    mut v_a_5613_: *mut leanh::LeanObject,
    mut v_a_5614_: *mut leanh::LeanObject,
    mut v_a_5615_: *mut leanh::LeanObject,
    mut v_a_5616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5617_ = l_Char_reduceLE(
        v_e_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_,
    );
    leanh::lean_dec(v_a_5615_);
    leanh::lean_dec_ref(v_a_5614_);
    leanh::lean_dec(v_a_5613_);
    leanh::lean_dec_ref(v_a_5612_);
    leanh::lean_dec(v_a_5611_);
    leanh::lean_dec_ref(v_a_5610_);
    leanh::lean_dec(v_a_5609_);
    return v_res_5617_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5636_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_;
    v___x_5637_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_;
    v___x_5638_ =
        leanh::lean_alloc_closure(l_Char_reduceLE___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5639_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5636_, v___x_5637_, v___x_5638_);
    return v___x_5639_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20____boxed(
    mut v_a_5640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5641_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_();
    return v_res_5641_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5642_ =
        leanh::lean_alloc_closure(l_Char_reduceLE___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5643_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5643_, 0, v___x_5642_);
    return v___x_5643_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: u8 = 0;
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5645_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_;
    v___x_5646_ = 1;
    v___x_5647_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_);
    v___x_5648_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5645_, v___x_5646_, v___x_5647_);
    return v___x_5648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22____boxed(
    mut v_a_5649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5650_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_();
    return v_res_5650_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: u8 = 0;
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5652_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_;
    v___x_5653_ = 1;
    v___x_5654_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_);
    v___x_5655_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5652_, v___x_5653_, v___x_5654_);
    return v___x_5655_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24____boxed(
    mut v_a_5656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5657_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24_();
    return v_res_5657_;
}
pub unsafe fn l_Char_reduceGT___redArg(
    mut v_e_5663_: *mut leanh::LeanObject,
    mut v_a_5664_: *mut leanh::LeanObject,
    mut v_a_5665_: *mut leanh::LeanObject,
    mut v_a_5666_: *mut leanh::LeanObject,
    mut v_a_5667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: u8 = 0;
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5680_: u8 = 0;
    let mut v_val_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v_val_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u32 = 0;
    let mut v___x_5690_: u32 = 0;
    let mut v___x_5691_: u8 = 0;
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5697_: u8 = 0;
    let mut v_a_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5701_: u8 = 0;
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5705_: u8 = 0;
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5710_: u8 = 0;
    let mut v_a_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5714_: u8 = 0;
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5669_ = l_Char_reduceGT___redArg___closed__2;
                v___x_5670_ = leanh::lean_unsigned_to_nat(4);
                v___x_5671_ = l_Lean_Expr_isAppOfArity(v_e_5663_, v___x_5669_, v___x_5670_);
                if v___x_5671_ == 0 {
                    leanh::lean_dec_ref(v_e_5663_);
                    v___x_5672_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_5673_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5673_, 0, v___x_5672_);
                    return v___x_5673_;
                } else {
                    v___x_5674_ = l_Lean_Expr_appFn_x21(v_e_5663_);
                    v___x_5675_ = l_Lean_Expr_appArg_x21(v___x_5674_);
                    leanh::lean_dec_ref(v___x_5674_);
                    v___x_5676_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5675_,
                        v_a_5664_,
                        v_a_5665_,
                        v_a_5666_,
                        v_a_5667_,
                    );
                    if leanh::lean_obj_tag(v___x_5676_) == 0 {
                        v_a_5677_ = leanh::lean_ctor_get(v___x_5676_, 0);
                        v_isSharedCheck_5710_ =
                            (!leanh::lean_is_exclusive(v___x_5676_)) as u8;
                        if v_isSharedCheck_5710_ == 0 {
                            v___x_5679_ = v___x_5676_;
                            v_isShared_5680_ = v_isSharedCheck_5710_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5677_);
                            leanh::lean_dec(v___x_5676_);
                            v___x_5679_ = leanh::lean_box(0);
                            v_isShared_5680_ = v_isSharedCheck_5710_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_5663_);
                        v_a_5711_ = leanh::lean_ctor_get(v___x_5676_, 0);
                        v_isSharedCheck_5718_ =
                            (!leanh::lean_is_exclusive(v___x_5676_)) as u8;
                        if v_isSharedCheck_5718_ == 0 {
                            v___x_5713_ = v___x_5676_;
                            v_isShared_5714_ = v_isSharedCheck_5718_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5711_);
                            leanh::lean_dec(v___x_5676_);
                            v___x_5713_ = leanh::lean_box(0);
                            v_isShared_5714_ = v_isSharedCheck_5718_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5677_) == 1 {
                    leanh::lean_del_object(v___x_5679_);
                    v_val_5681_ = leanh::lean_ctor_get(v_a_5677_, 0);
                    leanh::lean_inc(v_val_5681_);
                    leanh::lean_dec_ref_known(v_a_5677_, 1);
                    v___x_5682_ = l_Lean_Expr_appArg_x21(v_e_5663_);
                    v___x_5683_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5682_,
                        v_a_5664_,
                        v_a_5665_,
                        v_a_5666_,
                        v_a_5667_,
                    );
                    if leanh::lean_obj_tag(v___x_5683_) == 0 {
                        v_a_5684_ = leanh::lean_ctor_get(v___x_5683_, 0);
                        v_isSharedCheck_5697_ =
                            (!leanh::lean_is_exclusive(v___x_5683_)) as u8;
                        if v_isSharedCheck_5697_ == 0 {
                            v___x_5686_ = v___x_5683_;
                            v_isShared_5687_ = v_isSharedCheck_5697_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5684_);
                            leanh::lean_dec(v___x_5683_);
                            v___x_5686_ = leanh::lean_box(0);
                            v_isShared_5687_ = v_isSharedCheck_5697_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5681_);
                        leanh::lean_dec_ref(v_e_5663_);
                        v_a_5698_ = leanh::lean_ctor_get(v___x_5683_, 0);
                        v_isSharedCheck_5705_ =
                            (!leanh::lean_is_exclusive(v___x_5683_)) as u8;
                        if v_isSharedCheck_5705_ == 0 {
                            v___x_5700_ = v___x_5683_;
                            v_isShared_5701_ = v_isSharedCheck_5705_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5698_);
                            leanh::lean_dec(v___x_5683_);
                            v___x_5700_ = leanh::lean_box(0);
                            v_isShared_5701_ = v_isSharedCheck_5705_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5677_);
                    leanh::lean_dec_ref(v_e_5663_);
                    v___x_5706_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5680_ == 0 {
                        leanh::lean_ctor_set(v___x_5679_, 0, v___x_5706_);
                        v___x_5708_ = v___x_5679_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5709_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 0, v___x_5706_);
                        v___x_5708_ = v_reuseFailAlloc_5709_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5684_) == 1 {
                    leanh::lean_del_object(v___x_5686_);
                    v_val_5688_ = leanh::lean_ctor_get(v_a_5684_, 0);
                    leanh::lean_inc(v_val_5688_);
                    leanh::lean_dec_ref_known(v_a_5684_, 1);
                    v___x_5689_ = leanh::lean_unbox_uint32(v_val_5688_);
                    leanh::lean_dec(v_val_5688_);
                    v___x_5690_ = leanh::lean_unbox_uint32(v_val_5681_);
                    leanh::lean_dec(v_val_5681_);
                    v___x_5691_ = lean_uint32_dec_lt(v___x_5689_, v___x_5690_);
                    v___x_5692_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_5663_,
                        v___x_5691_,
                        v_a_5664_,
                        v_a_5665_,
                        v_a_5666_,
                        v_a_5667_,
                    );
                    return v___x_5692_;
                } else {
                    leanh::lean_dec(v_a_5684_);
                    leanh::lean_dec(v_val_5681_);
                    leanh::lean_dec_ref(v_e_5663_);
                    v___x_5693_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5687_ == 0 {
                        leanh::lean_ctor_set(v___x_5686_, 0, v___x_5693_);
                        v___x_5695_ = v___x_5686_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5693_);
                        v___x_5695_ = v_reuseFailAlloc_5696_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5695_;
            }
            4 => {
                if v_isShared_5701_ == 0 {
                    v___x_5703_ = v___x_5700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5698_);
                    v___x_5703_ = v_reuseFailAlloc_5704_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5703_;
            }
            6 => {
                return v___x_5708_;
            }
            7 => {
                if v_isShared_5714_ == 0 {
                    v___x_5716_ = v___x_5713_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5717_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_a_5711_);
                    v___x_5716_ = v_reuseFailAlloc_5717_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceGT___redArg___boxed(
    mut v_e_5719_: *mut leanh::LeanObject,
    mut v_a_5720_: *mut leanh::LeanObject,
    mut v_a_5721_: *mut leanh::LeanObject,
    mut v_a_5722_: *mut leanh::LeanObject,
    mut v_a_5723_: *mut leanh::LeanObject,
    mut v_a_5724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5725_ = l_Char_reduceGT___redArg(v_e_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_);
    leanh::lean_dec(v_a_5723_);
    leanh::lean_dec_ref(v_a_5722_);
    leanh::lean_dec(v_a_5721_);
    leanh::lean_dec_ref(v_a_5720_);
    return v_res_5725_;
}
pub unsafe fn l_Char_reduceGT(
    mut v_e_5726_: *mut leanh::LeanObject,
    mut v_a_5727_: *mut leanh::LeanObject,
    mut v_a_5728_: *mut leanh::LeanObject,
    mut v_a_5729_: *mut leanh::LeanObject,
    mut v_a_5730_: *mut leanh::LeanObject,
    mut v_a_5731_: *mut leanh::LeanObject,
    mut v_a_5732_: *mut leanh::LeanObject,
    mut v_a_5733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5735_ = l_Char_reduceGT___redArg(v_e_5726_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_);
    return v___x_5735_;
}
pub unsafe fn l_Char_reduceGT___boxed(
    mut v_e_5736_: *mut leanh::LeanObject,
    mut v_a_5737_: *mut leanh::LeanObject,
    mut v_a_5738_: *mut leanh::LeanObject,
    mut v_a_5739_: *mut leanh::LeanObject,
    mut v_a_5740_: *mut leanh::LeanObject,
    mut v_a_5741_: *mut leanh::LeanObject,
    mut v_a_5742_: *mut leanh::LeanObject,
    mut v_a_5743_: *mut leanh::LeanObject,
    mut v_a_5744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5745_ = l_Char_reduceGT(
        v_e_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_,
    );
    leanh::lean_dec(v_a_5743_);
    leanh::lean_dec_ref(v_a_5742_);
    leanh::lean_dec(v_a_5741_);
    leanh::lean_dec_ref(v_a_5740_);
    leanh::lean_dec(v_a_5739_);
    leanh::lean_dec_ref(v_a_5738_);
    leanh::lean_dec(v_a_5737_);
    return v_res_5745_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5751_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_;
    v___x_5752_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_;
    v___x_5753_ =
        leanh::lean_alloc_closure(l_Char_reduceGT___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5754_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5751_, v___x_5752_, v___x_5753_);
    return v___x_5754_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20____boxed(
    mut v_a_5755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5756_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_();
    return v_res_5756_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5757_ =
        leanh::lean_alloc_closure(l_Char_reduceGT___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5758_, 0, v___x_5757_);
    return v___x_5758_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: u8 = 0;
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5760_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_;
    v___x_5761_ = 1;
    v___x_5762_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_);
    v___x_5763_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5760_, v___x_5761_, v___x_5762_);
    return v___x_5763_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22____boxed(
    mut v_a_5764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5765_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_();
    return v_res_5765_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: u8 = 0;
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5767_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_;
    v___x_5768_ = 1;
    v___x_5769_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_);
    v___x_5770_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5767_, v___x_5768_, v___x_5769_);
    return v___x_5770_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24____boxed(
    mut v_a_5771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5772_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24_();
    return v_res_5772_;
}
pub unsafe fn l_Char_reduceGE___redArg(
    mut v_e_5778_: *mut leanh::LeanObject,
    mut v_a_5779_: *mut leanh::LeanObject,
    mut v_a_5780_: *mut leanh::LeanObject,
    mut v_a_5781_: *mut leanh::LeanObject,
    mut v_a_5782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: u8 = 0;
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v_val_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5802_: u8 = 0;
    let mut v_val_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: u32 = 0;
    let mut v___x_5805_: u32 = 0;
    let mut v___x_5806_: u8 = 0;
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5812_: u8 = 0;
    let mut v_a_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5816_: u8 = 0;
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5820_: u8 = 0;
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5825_: u8 = 0;
    let mut v_a_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5784_ = l_Char_reduceGE___redArg___closed__2;
                v___x_5785_ = leanh::lean_unsigned_to_nat(4);
                v___x_5786_ = l_Lean_Expr_isAppOfArity(v_e_5778_, v___x_5784_, v___x_5785_);
                if v___x_5786_ == 0 {
                    leanh::lean_dec_ref(v_e_5778_);
                    v___x_5787_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_5788_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5788_, 0, v___x_5787_);
                    return v___x_5788_;
                } else {
                    v___x_5789_ = l_Lean_Expr_appFn_x21(v_e_5778_);
                    v___x_5790_ = l_Lean_Expr_appArg_x21(v___x_5789_);
                    leanh::lean_dec_ref(v___x_5789_);
                    v___x_5791_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5790_,
                        v_a_5779_,
                        v_a_5780_,
                        v_a_5781_,
                        v_a_5782_,
                    );
                    if leanh::lean_obj_tag(v___x_5791_) == 0 {
                        v_a_5792_ = leanh::lean_ctor_get(v___x_5791_, 0);
                        v_isSharedCheck_5825_ =
                            (!leanh::lean_is_exclusive(v___x_5791_)) as u8;
                        if v_isSharedCheck_5825_ == 0 {
                            v___x_5794_ = v___x_5791_;
                            v_isShared_5795_ = v_isSharedCheck_5825_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5792_);
                            leanh::lean_dec(v___x_5791_);
                            v___x_5794_ = leanh::lean_box(0);
                            v_isShared_5795_ = v_isSharedCheck_5825_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_5778_);
                        v_a_5826_ = leanh::lean_ctor_get(v___x_5791_, 0);
                        v_isSharedCheck_5833_ =
                            (!leanh::lean_is_exclusive(v___x_5791_)) as u8;
                        if v_isSharedCheck_5833_ == 0 {
                            v___x_5828_ = v___x_5791_;
                            v_isShared_5829_ = v_isSharedCheck_5833_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5826_);
                            leanh::lean_dec(v___x_5791_);
                            v___x_5828_ = leanh::lean_box(0);
                            v_isShared_5829_ = v_isSharedCheck_5833_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5792_) == 1 {
                    leanh::lean_del_object(v___x_5794_);
                    v_val_5796_ = leanh::lean_ctor_get(v_a_5792_, 0);
                    leanh::lean_inc(v_val_5796_);
                    leanh::lean_dec_ref_known(v_a_5792_, 1);
                    v___x_5797_ = l_Lean_Expr_appArg_x21(v_e_5778_);
                    v___x_5798_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5797_,
                        v_a_5779_,
                        v_a_5780_,
                        v_a_5781_,
                        v_a_5782_,
                    );
                    if leanh::lean_obj_tag(v___x_5798_) == 0 {
                        v_a_5799_ = leanh::lean_ctor_get(v___x_5798_, 0);
                        v_isSharedCheck_5812_ =
                            (!leanh::lean_is_exclusive(v___x_5798_)) as u8;
                        if v_isSharedCheck_5812_ == 0 {
                            v___x_5801_ = v___x_5798_;
                            v_isShared_5802_ = v_isSharedCheck_5812_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5799_);
                            leanh::lean_dec(v___x_5798_);
                            v___x_5801_ = leanh::lean_box(0);
                            v_isShared_5802_ = v_isSharedCheck_5812_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5796_);
                        leanh::lean_dec_ref(v_e_5778_);
                        v_a_5813_ = leanh::lean_ctor_get(v___x_5798_, 0);
                        v_isSharedCheck_5820_ =
                            (!leanh::lean_is_exclusive(v___x_5798_)) as u8;
                        if v_isSharedCheck_5820_ == 0 {
                            v___x_5815_ = v___x_5798_;
                            v_isShared_5816_ = v_isSharedCheck_5820_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5813_);
                            leanh::lean_dec(v___x_5798_);
                            v___x_5815_ = leanh::lean_box(0);
                            v_isShared_5816_ = v_isSharedCheck_5820_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5792_);
                    leanh::lean_dec_ref(v_e_5778_);
                    v___x_5821_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5795_ == 0 {
                        leanh::lean_ctor_set(v___x_5794_, 0, v___x_5821_);
                        v___x_5823_ = v___x_5794_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5824_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5824_, 0, v___x_5821_);
                        v___x_5823_ = v_reuseFailAlloc_5824_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5799_) == 1 {
                    leanh::lean_del_object(v___x_5801_);
                    v_val_5803_ = leanh::lean_ctor_get(v_a_5799_, 0);
                    leanh::lean_inc(v_val_5803_);
                    leanh::lean_dec_ref_known(v_a_5799_, 1);
                    v___x_5804_ = leanh::lean_unbox_uint32(v_val_5803_);
                    leanh::lean_dec(v_val_5803_);
                    v___x_5805_ = leanh::lean_unbox_uint32(v_val_5796_);
                    leanh::lean_dec(v_val_5796_);
                    v___x_5806_ = lean_uint32_dec_le(v___x_5804_, v___x_5805_);
                    v___x_5807_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_5778_,
                        v___x_5806_,
                        v_a_5779_,
                        v_a_5780_,
                        v_a_5781_,
                        v_a_5782_,
                    );
                    return v___x_5807_;
                } else {
                    leanh::lean_dec(v_a_5799_);
                    leanh::lean_dec(v_val_5796_);
                    leanh::lean_dec_ref(v_e_5778_);
                    v___x_5808_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5802_ == 0 {
                        leanh::lean_ctor_set(v___x_5801_, 0, v___x_5808_);
                        v___x_5810_ = v___x_5801_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5811_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5811_, 0, v___x_5808_);
                        v___x_5810_ = v_reuseFailAlloc_5811_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5810_;
            }
            4 => {
                if v_isShared_5816_ == 0 {
                    v___x_5818_ = v___x_5815_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5819_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_a_5813_);
                    v___x_5818_ = v_reuseFailAlloc_5819_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5818_;
            }
            6 => {
                return v___x_5823_;
            }
            7 => {
                if v_isShared_5829_ == 0 {
                    v___x_5831_ = v___x_5828_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
                    v___x_5831_ = v_reuseFailAlloc_5832_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceGE___redArg___boxed(
    mut v_e_5834_: *mut leanh::LeanObject,
    mut v_a_5835_: *mut leanh::LeanObject,
    mut v_a_5836_: *mut leanh::LeanObject,
    mut v_a_5837_: *mut leanh::LeanObject,
    mut v_a_5838_: *mut leanh::LeanObject,
    mut v_a_5839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5840_ = l_Char_reduceGE___redArg(v_e_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_);
    leanh::lean_dec(v_a_5838_);
    leanh::lean_dec_ref(v_a_5837_);
    leanh::lean_dec(v_a_5836_);
    leanh::lean_dec_ref(v_a_5835_);
    return v_res_5840_;
}
pub unsafe fn l_Char_reduceGE(
    mut v_e_5841_: *mut leanh::LeanObject,
    mut v_a_5842_: *mut leanh::LeanObject,
    mut v_a_5843_: *mut leanh::LeanObject,
    mut v_a_5844_: *mut leanh::LeanObject,
    mut v_a_5845_: *mut leanh::LeanObject,
    mut v_a_5846_: *mut leanh::LeanObject,
    mut v_a_5847_: *mut leanh::LeanObject,
    mut v_a_5848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5850_ = l_Char_reduceGE___redArg(v_e_5841_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_);
    return v___x_5850_;
}
pub unsafe fn l_Char_reduceGE___boxed(
    mut v_e_5851_: *mut leanh::LeanObject,
    mut v_a_5852_: *mut leanh::LeanObject,
    mut v_a_5853_: *mut leanh::LeanObject,
    mut v_a_5854_: *mut leanh::LeanObject,
    mut v_a_5855_: *mut leanh::LeanObject,
    mut v_a_5856_: *mut leanh::LeanObject,
    mut v_a_5857_: *mut leanh::LeanObject,
    mut v_a_5858_: *mut leanh::LeanObject,
    mut v_a_5859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5860_ = l_Char_reduceGE(
        v_e_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_,
    );
    leanh::lean_dec(v_a_5858_);
    leanh::lean_dec_ref(v_a_5857_);
    leanh::lean_dec(v_a_5856_);
    leanh::lean_dec_ref(v_a_5855_);
    leanh::lean_dec(v_a_5854_);
    leanh::lean_dec_ref(v_a_5853_);
    leanh::lean_dec(v_a_5852_);
    return v_res_5860_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5866_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_;
    v___x_5867_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_;
    v___x_5868_ =
        leanh::lean_alloc_closure(l_Char_reduceGE___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5869_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5866_, v___x_5867_, v___x_5868_);
    return v___x_5869_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20____boxed(
    mut v_a_5870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5871_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_();
    return v_res_5871_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5872_ =
        leanh::lean_alloc_closure(l_Char_reduceGE___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5873_, 0, v___x_5872_);
    return v___x_5873_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: u8 = 0;
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5875_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_;
    v___x_5876_ = 1;
    v___x_5877_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_);
    v___x_5878_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_5875_, v___x_5876_, v___x_5877_);
    return v___x_5878_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22____boxed(
    mut v_a_5879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5880_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_();
    return v_res_5880_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: u8 = 0;
    let mut v___x_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5882_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_;
    v___x_5883_ = 1;
    v___x_5884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_);
    v___x_5885_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_5882_, v___x_5883_, v___x_5884_);
    return v___x_5885_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24____boxed(
    mut v_a_5886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5887_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24_();
    return v_res_5887_;
}
pub unsafe fn l_Char_reduceEq___redArg(
    mut v_e_5891_: *mut leanh::LeanObject,
    mut v_a_5892_: *mut leanh::LeanObject,
    mut v_a_5893_: *mut leanh::LeanObject,
    mut v_a_5894_: *mut leanh::LeanObject,
    mut v_a_5895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: u8 = 0;
    let mut v___x_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5908_: u8 = 0;
    let mut v_val_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5915_: u8 = 0;
    let mut v_val_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: u32 = 0;
    let mut v___x_5918_: u32 = 0;
    let mut v___x_5919_: u8 = 0;
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5925_: u8 = 0;
    let mut v_a_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5929_: u8 = 0;
    let mut v___x_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5933_: u8 = 0;
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5938_: u8 = 0;
    let mut v_a_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5942_: u8 = 0;
    let mut v___x_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5897_ = l_Char_reduceEq___redArg___closed__1;
                v___x_5898_ = leanh::lean_unsigned_to_nat(3);
                v___x_5899_ = l_Lean_Expr_isAppOfArity(v_e_5891_, v___x_5897_, v___x_5898_);
                if v___x_5899_ == 0 {
                    leanh::lean_dec_ref(v_e_5891_);
                    v___x_5900_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_5901_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5901_, 0, v___x_5900_);
                    return v___x_5901_;
                } else {
                    v___x_5902_ = l_Lean_Expr_appFn_x21(v_e_5891_);
                    v___x_5903_ = l_Lean_Expr_appArg_x21(v___x_5902_);
                    leanh::lean_dec_ref(v___x_5902_);
                    v___x_5904_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5903_,
                        v_a_5892_,
                        v_a_5893_,
                        v_a_5894_,
                        v_a_5895_,
                    );
                    if leanh::lean_obj_tag(v___x_5904_) == 0 {
                        v_a_5905_ = leanh::lean_ctor_get(v___x_5904_, 0);
                        v_isSharedCheck_5938_ =
                            (!leanh::lean_is_exclusive(v___x_5904_)) as u8;
                        if v_isSharedCheck_5938_ == 0 {
                            v___x_5907_ = v___x_5904_;
                            v_isShared_5908_ = v_isSharedCheck_5938_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5905_);
                            leanh::lean_dec(v___x_5904_);
                            v___x_5907_ = leanh::lean_box(0);
                            v_isShared_5908_ = v_isSharedCheck_5938_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_5891_);
                        v_a_5939_ = leanh::lean_ctor_get(v___x_5904_, 0);
                        v_isSharedCheck_5946_ =
                            (!leanh::lean_is_exclusive(v___x_5904_)) as u8;
                        if v_isSharedCheck_5946_ == 0 {
                            v___x_5941_ = v___x_5904_;
                            v_isShared_5942_ = v_isSharedCheck_5946_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5939_);
                            leanh::lean_dec(v___x_5904_);
                            v___x_5941_ = leanh::lean_box(0);
                            v_isShared_5942_ = v_isSharedCheck_5946_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5905_) == 1 {
                    leanh::lean_del_object(v___x_5907_);
                    v_val_5909_ = leanh::lean_ctor_get(v_a_5905_, 0);
                    leanh::lean_inc(v_val_5909_);
                    leanh::lean_dec_ref_known(v_a_5905_, 1);
                    v___x_5910_ = l_Lean_Expr_appArg_x21(v_e_5891_);
                    v___x_5911_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_5910_,
                        v_a_5892_,
                        v_a_5893_,
                        v_a_5894_,
                        v_a_5895_,
                    );
                    if leanh::lean_obj_tag(v___x_5911_) == 0 {
                        v_a_5912_ = leanh::lean_ctor_get(v___x_5911_, 0);
                        v_isSharedCheck_5925_ =
                            (!leanh::lean_is_exclusive(v___x_5911_)) as u8;
                        if v_isSharedCheck_5925_ == 0 {
                            v___x_5914_ = v___x_5911_;
                            v_isShared_5915_ = v_isSharedCheck_5925_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5912_);
                            leanh::lean_dec(v___x_5911_);
                            v___x_5914_ = leanh::lean_box(0);
                            v_isShared_5915_ = v_isSharedCheck_5925_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5909_);
                        leanh::lean_dec_ref(v_e_5891_);
                        v_a_5926_ = leanh::lean_ctor_get(v___x_5911_, 0);
                        v_isSharedCheck_5933_ =
                            (!leanh::lean_is_exclusive(v___x_5911_)) as u8;
                        if v_isSharedCheck_5933_ == 0 {
                            v___x_5928_ = v___x_5911_;
                            v_isShared_5929_ = v_isSharedCheck_5933_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5926_);
                            leanh::lean_dec(v___x_5911_);
                            v___x_5928_ = leanh::lean_box(0);
                            v_isShared_5929_ = v_isSharedCheck_5933_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5905_);
                    leanh::lean_dec_ref(v_e_5891_);
                    v___x_5934_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5908_ == 0 {
                        leanh::lean_ctor_set(v___x_5907_, 0, v___x_5934_);
                        v___x_5936_ = v___x_5907_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5937_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5937_, 0, v___x_5934_);
                        v___x_5936_ = v_reuseFailAlloc_5937_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5912_) == 1 {
                    leanh::lean_del_object(v___x_5914_);
                    v_val_5916_ = leanh::lean_ctor_get(v_a_5912_, 0);
                    leanh::lean_inc(v_val_5916_);
                    leanh::lean_dec_ref_known(v_a_5912_, 1);
                    v___x_5917_ = leanh::lean_unbox_uint32(v_val_5909_);
                    leanh::lean_dec(v_val_5909_);
                    v___x_5918_ = leanh::lean_unbox_uint32(v_val_5916_);
                    leanh::lean_dec(v_val_5916_);
                    v___x_5919_ = lean_uint32_dec_eq(v___x_5917_, v___x_5918_);
                    v___x_5920_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_5891_,
                        v___x_5919_,
                        v_a_5892_,
                        v_a_5893_,
                        v_a_5894_,
                        v_a_5895_,
                    );
                    return v___x_5920_;
                } else {
                    leanh::lean_dec(v_a_5912_);
                    leanh::lean_dec(v_val_5909_);
                    leanh::lean_dec_ref(v_e_5891_);
                    v___x_5921_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_5915_ == 0 {
                        leanh::lean_ctor_set(v___x_5914_, 0, v___x_5921_);
                        v___x_5923_ = v___x_5914_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5924_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5924_, 0, v___x_5921_);
                        v___x_5923_ = v_reuseFailAlloc_5924_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5923_;
            }
            4 => {
                if v_isShared_5929_ == 0 {
                    v___x_5931_ = v___x_5928_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5932_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_a_5926_);
                    v___x_5931_ = v_reuseFailAlloc_5932_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5931_;
            }
            6 => {
                return v___x_5936_;
            }
            7 => {
                if v_isShared_5942_ == 0 {
                    v___x_5944_ = v___x_5941_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_a_5939_);
                    v___x_5944_ = v_reuseFailAlloc_5945_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceEq___redArg___boxed(
    mut v_e_5947_: *mut leanh::LeanObject,
    mut v_a_5948_: *mut leanh::LeanObject,
    mut v_a_5949_: *mut leanh::LeanObject,
    mut v_a_5950_: *mut leanh::LeanObject,
    mut v_a_5951_: *mut leanh::LeanObject,
    mut v_a_5952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5953_ = l_Char_reduceEq___redArg(v_e_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_);
    leanh::lean_dec(v_a_5951_);
    leanh::lean_dec_ref(v_a_5950_);
    leanh::lean_dec(v_a_5949_);
    leanh::lean_dec_ref(v_a_5948_);
    return v_res_5953_;
}
pub unsafe fn l_Char_reduceEq(
    mut v_e_5954_: *mut leanh::LeanObject,
    mut v_a_5955_: *mut leanh::LeanObject,
    mut v_a_5956_: *mut leanh::LeanObject,
    mut v_a_5957_: *mut leanh::LeanObject,
    mut v_a_5958_: *mut leanh::LeanObject,
    mut v_a_5959_: *mut leanh::LeanObject,
    mut v_a_5960_: *mut leanh::LeanObject,
    mut v_a_5961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5963_ = l_Char_reduceEq___redArg(v_e_5954_, v_a_5958_, v_a_5959_, v_a_5960_, v_a_5961_);
    return v___x_5963_;
}
pub unsafe fn l_Char_reduceEq___boxed(
    mut v_e_5964_: *mut leanh::LeanObject,
    mut v_a_5965_: *mut leanh::LeanObject,
    mut v_a_5966_: *mut leanh::LeanObject,
    mut v_a_5967_: *mut leanh::LeanObject,
    mut v_a_5968_: *mut leanh::LeanObject,
    mut v_a_5969_: *mut leanh::LeanObject,
    mut v_a_5970_: *mut leanh::LeanObject,
    mut v_a_5971_: *mut leanh::LeanObject,
    mut v_a_5972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5973_ = l_Char_reduceEq(
        v_e_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_,
    );
    leanh::lean_dec(v_a_5971_);
    leanh::lean_dec_ref(v_a_5970_);
    leanh::lean_dec(v_a_5969_);
    leanh::lean_dec_ref(v_a_5968_);
    leanh::lean_dec(v_a_5967_);
    leanh::lean_dec_ref(v_a_5966_);
    leanh::lean_dec(v_a_5965_);
    return v_res_5973_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5991_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_;
    v___x_5992_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_;
    v___x_5993_ =
        leanh::lean_alloc_closure(l_Char_reduceEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5994_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5991_, v___x_5992_, v___x_5993_);
    return v___x_5994_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20____boxed(
    mut v_a_5995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5996_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_();
    return v_res_5996_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5997_ =
        leanh::lean_alloc_closure(l_Char_reduceEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_5998_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5998_, 0, v___x_5997_);
    return v___x_5998_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: u8 = 0;
    let mut v___x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6000_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_;
    v___x_6001_ = 1;
    v___x_6002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_);
    v___x_6003_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_6000_, v___x_6001_, v___x_6002_);
    return v___x_6003_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22____boxed(
    mut v_a_6004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6005_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_();
    return v_res_6005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: u8 = 0;
    let mut v___x_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6007_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_;
    v___x_6008_ = 1;
    v___x_6009_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_);
    v___x_6010_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_6007_, v___x_6008_, v___x_6009_);
    return v___x_6010_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24____boxed(
    mut v_a_6011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6012_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24_();
    return v_res_6012_;
}
pub unsafe fn l_Char_reduceNe___redArg(
    mut v_e_6016_: *mut leanh::LeanObject,
    mut v_a_6017_: *mut leanh::LeanObject,
    mut v_a_6018_: *mut leanh::LeanObject,
    mut v_a_6019_: *mut leanh::LeanObject,
    mut v_a_6020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: u8 = 0;
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6033_: u8 = 0;
    let mut v_val_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v_val_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: u32 = 0;
    let mut v___x_6043_: u32 = 0;
    let mut v___x_6044_: u8 = 0;
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_a_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6056_: u8 = 0;
    let mut v___x_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6060_: u8 = 0;
    let mut v___x_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v_a_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6022_ = l_Char_reduceNe___redArg___closed__1;
                v___x_6023_ = leanh::lean_unsigned_to_nat(3);
                v___x_6024_ = l_Lean_Expr_isAppOfArity(v_e_6016_, v___x_6022_, v___x_6023_);
                if v___x_6024_ == 0 {
                    leanh::lean_dec_ref(v_e_6016_);
                    v___x_6025_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_6026_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6026_, 0, v___x_6025_);
                    return v___x_6026_;
                } else {
                    v___x_6027_ = l_Lean_Expr_appFn_x21(v_e_6016_);
                    v___x_6028_ = l_Lean_Expr_appArg_x21(v___x_6027_);
                    leanh::lean_dec_ref(v___x_6027_);
                    v___x_6029_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_6028_,
                        v_a_6017_,
                        v_a_6018_,
                        v_a_6019_,
                        v_a_6020_,
                    );
                    if leanh::lean_obj_tag(v___x_6029_) == 0 {
                        v_a_6030_ = leanh::lean_ctor_get(v___x_6029_, 0);
                        v_isSharedCheck_6065_ =
                            (!leanh::lean_is_exclusive(v___x_6029_)) as u8;
                        if v_isSharedCheck_6065_ == 0 {
                            v___x_6032_ = v___x_6029_;
                            v_isShared_6033_ = v_isSharedCheck_6065_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6030_);
                            leanh::lean_dec(v___x_6029_);
                            v___x_6032_ = leanh::lean_box(0);
                            v_isShared_6033_ = v_isSharedCheck_6065_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_6016_);
                        v_a_6066_ = leanh::lean_ctor_get(v___x_6029_, 0);
                        v_isSharedCheck_6073_ =
                            (!leanh::lean_is_exclusive(v___x_6029_)) as u8;
                        if v_isSharedCheck_6073_ == 0 {
                            v___x_6068_ = v___x_6029_;
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6066_);
                            leanh::lean_dec(v___x_6029_);
                            v___x_6068_ = leanh::lean_box(0);
                            v_isShared_6069_ = v_isSharedCheck_6073_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6030_) == 1 {
                    leanh::lean_del_object(v___x_6032_);
                    v_val_6034_ = leanh::lean_ctor_get(v_a_6030_, 0);
                    leanh::lean_inc(v_val_6034_);
                    leanh::lean_dec_ref_known(v_a_6030_, 1);
                    v___x_6035_ = l_Lean_Expr_appArg_x21(v_e_6016_);
                    v___x_6036_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_6035_,
                        v_a_6017_,
                        v_a_6018_,
                        v_a_6019_,
                        v_a_6020_,
                    );
                    if leanh::lean_obj_tag(v___x_6036_) == 0 {
                        v_a_6037_ = leanh::lean_ctor_get(v___x_6036_, 0);
                        v_isSharedCheck_6052_ =
                            (!leanh::lean_is_exclusive(v___x_6036_)) as u8;
                        if v_isSharedCheck_6052_ == 0 {
                            v___x_6039_ = v___x_6036_;
                            v_isShared_6040_ = v_isSharedCheck_6052_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6037_);
                            leanh::lean_dec(v___x_6036_);
                            v___x_6039_ = leanh::lean_box(0);
                            v_isShared_6040_ = v_isSharedCheck_6052_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_6034_);
                        leanh::lean_dec_ref(v_e_6016_);
                        v_a_6053_ = leanh::lean_ctor_get(v___x_6036_, 0);
                        v_isSharedCheck_6060_ =
                            (!leanh::lean_is_exclusive(v___x_6036_)) as u8;
                        if v_isSharedCheck_6060_ == 0 {
                            v___x_6055_ = v___x_6036_;
                            v_isShared_6056_ = v_isSharedCheck_6060_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6053_);
                            leanh::lean_dec(v___x_6036_);
                            v___x_6055_ = leanh::lean_box(0);
                            v_isShared_6056_ = v_isSharedCheck_6060_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6030_);
                    leanh::lean_dec_ref(v_e_6016_);
                    v___x_6061_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_6033_ == 0 {
                        leanh::lean_ctor_set(v___x_6032_, 0, v___x_6061_);
                        v___x_6063_ = v___x_6032_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6064_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6064_, 0, v___x_6061_);
                        v___x_6063_ = v_reuseFailAlloc_6064_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_6037_) == 1 {
                    leanh::lean_del_object(v___x_6039_);
                    v_val_6041_ = leanh::lean_ctor_get(v_a_6037_, 0);
                    leanh::lean_inc(v_val_6041_);
                    leanh::lean_dec_ref_known(v_a_6037_, 1);
                    v___x_6042_ = leanh::lean_unbox_uint32(v_val_6034_);
                    leanh::lean_dec(v_val_6034_);
                    v___x_6043_ = leanh::lean_unbox_uint32(v_val_6041_);
                    leanh::lean_dec(v_val_6041_);
                    v___x_6044_ = lean_uint32_dec_eq(v___x_6042_, v___x_6043_);
                    if v___x_6044_ == 0 {
                        v___x_6045_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                            v_e_6016_,
                            v___x_6024_,
                            v_a_6017_,
                            v_a_6018_,
                            v_a_6019_,
                            v_a_6020_,
                        );
                        return v___x_6045_;
                    } else {
                        v___x_6046_ = 0;
                        v___x_6047_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                            v_e_6016_,
                            v___x_6046_,
                            v_a_6017_,
                            v_a_6018_,
                            v_a_6019_,
                            v_a_6020_,
                        );
                        return v___x_6047_;
                    }
                } else {
                    leanh::lean_dec(v_a_6037_);
                    leanh::lean_dec(v_val_6034_);
                    leanh::lean_dec_ref(v_e_6016_);
                    v___x_6048_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_6040_ == 0 {
                        leanh::lean_ctor_set(v___x_6039_, 0, v___x_6048_);
                        v___x_6050_ = v___x_6039_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 0, v___x_6048_);
                        v___x_6050_ = v_reuseFailAlloc_6051_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6050_;
            }
            4 => {
                if v_isShared_6056_ == 0 {
                    v___x_6058_ = v___x_6055_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6059_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_a_6053_);
                    v___x_6058_ = v_reuseFailAlloc_6059_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6058_;
            }
            6 => {
                return v___x_6063_;
            }
            7 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceNe___redArg___boxed(
    mut v_e_6074_: *mut leanh::LeanObject,
    mut v_a_6075_: *mut leanh::LeanObject,
    mut v_a_6076_: *mut leanh::LeanObject,
    mut v_a_6077_: *mut leanh::LeanObject,
    mut v_a_6078_: *mut leanh::LeanObject,
    mut v_a_6079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6080_ = l_Char_reduceNe___redArg(v_e_6074_, v_a_6075_, v_a_6076_, v_a_6077_, v_a_6078_);
    leanh::lean_dec(v_a_6078_);
    leanh::lean_dec_ref(v_a_6077_);
    leanh::lean_dec(v_a_6076_);
    leanh::lean_dec_ref(v_a_6075_);
    return v_res_6080_;
}
pub unsafe fn l_Char_reduceNe(
    mut v_e_6081_: *mut leanh::LeanObject,
    mut v_a_6082_: *mut leanh::LeanObject,
    mut v_a_6083_: *mut leanh::LeanObject,
    mut v_a_6084_: *mut leanh::LeanObject,
    mut v_a_6085_: *mut leanh::LeanObject,
    mut v_a_6086_: *mut leanh::LeanObject,
    mut v_a_6087_: *mut leanh::LeanObject,
    mut v_a_6088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6090_ = l_Char_reduceNe___redArg(v_e_6081_, v_a_6085_, v_a_6086_, v_a_6087_, v_a_6088_);
    return v___x_6090_;
}
pub unsafe fn l_Char_reduceNe___boxed(
    mut v_e_6091_: *mut leanh::LeanObject,
    mut v_a_6092_: *mut leanh::LeanObject,
    mut v_a_6093_: *mut leanh::LeanObject,
    mut v_a_6094_: *mut leanh::LeanObject,
    mut v_a_6095_: *mut leanh::LeanObject,
    mut v_a_6096_: *mut leanh::LeanObject,
    mut v_a_6097_: *mut leanh::LeanObject,
    mut v_a_6098_: *mut leanh::LeanObject,
    mut v_a_6099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6100_ = l_Char_reduceNe(
        v_e_6091_, v_a_6092_, v_a_6093_, v_a_6094_, v_a_6095_, v_a_6096_, v_a_6097_, v_a_6098_,
    );
    leanh::lean_dec(v_a_6098_);
    leanh::lean_dec_ref(v_a_6097_);
    leanh::lean_dec(v_a_6096_);
    leanh::lean_dec_ref(v_a_6095_);
    leanh::lean_dec(v_a_6094_);
    leanh::lean_dec_ref(v_a_6093_);
    leanh::lean_dec(v_a_6092_);
    return v_res_6100_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6123_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_;
    v___x_6124_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_;
    v___x_6125_ =
        leanh::lean_alloc_closure(l_Char_reduceNe___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_6126_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_6123_, v___x_6124_, v___x_6125_);
    return v___x_6126_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20____boxed(
    mut v_a_6127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6128_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_();
    return v_res_6128_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6129_ =
        leanh::lean_alloc_closure(l_Char_reduceNe___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_6130_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6130_, 0, v___x_6129_);
    return v___x_6130_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: u8 = 0;
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6132_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_;
    v___x_6133_ = 1;
    v___x_6134_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_);
    v___x_6135_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_6132_, v___x_6133_, v___x_6134_);
    return v___x_6135_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22____boxed(
    mut v_a_6136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6137_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_();
    return v_res_6137_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: u8 = 0;
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6139_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_;
    v___x_6140_ = 1;
    v___x_6141_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_);
    v___x_6142_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_6139_, v___x_6140_, v___x_6141_);
    return v___x_6142_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24____boxed(
    mut v_a_6143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6144_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24_();
    return v_res_6144_;
}
pub unsafe fn l_Char_reduceBEq___redArg(
    mut v_e_6150_: *mut leanh::LeanObject,
    mut v_a_6151_: *mut leanh::LeanObject,
    mut v_a_6152_: *mut leanh::LeanObject,
    mut v_a_6153_: *mut leanh::LeanObject,
    mut v_a_6154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: u8 = 0;
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6167_: u8 = 0;
    let mut v_val_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6171_: u8 = 0;
    let mut v___x_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___y_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: u32 = 0;
    let mut v___x_6188_: u32 = 0;
    let mut v___x_6189_: u8 = 0;
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6196_: u8 = 0;
    let mut v_a_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6200_: u8 = 0;
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6204_: u8 = 0;
    let mut v_isSharedCheck_6205_: u8 = 0;
    let mut v___x_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_a_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6214_: u8 = 0;
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6156_ = l_Char_reduceBEq___redArg___closed__2;
                v___x_6157_ = leanh::lean_unsigned_to_nat(4);
                v___x_6158_ = l_Lean_Expr_isAppOfArity(v_e_6150_, v___x_6156_, v___x_6157_);
                if v___x_6158_ == 0 {
                    v___x_6159_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_6160_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6160_, 0, v___x_6159_);
                    return v___x_6160_;
                } else {
                    v___x_6161_ = l_Lean_Expr_appFn_x21(v_e_6150_);
                    v___x_6162_ = l_Lean_Expr_appArg_x21(v___x_6161_);
                    leanh::lean_dec_ref(v___x_6161_);
                    v___x_6163_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_6162_,
                        v_a_6151_,
                        v_a_6152_,
                        v_a_6153_,
                        v_a_6154_,
                    );
                    if leanh::lean_obj_tag(v___x_6163_) == 0 {
                        v_a_6164_ = leanh::lean_ctor_get(v___x_6163_, 0);
                        v_isSharedCheck_6210_ =
                            (!leanh::lean_is_exclusive(v___x_6163_)) as u8;
                        if v_isSharedCheck_6210_ == 0 {
                            v___x_6166_ = v___x_6163_;
                            v_isShared_6167_ = v_isSharedCheck_6210_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6164_);
                            leanh::lean_dec(v___x_6163_);
                            v___x_6166_ = leanh::lean_box(0);
                            v_isShared_6167_ = v_isSharedCheck_6210_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6211_ = leanh::lean_ctor_get(v___x_6163_, 0);
                        v_isSharedCheck_6218_ =
                            (!leanh::lean_is_exclusive(v___x_6163_)) as u8;
                        if v_isSharedCheck_6218_ == 0 {
                            v___x_6213_ = v___x_6163_;
                            v_isShared_6214_ = v_isSharedCheck_6218_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6211_);
                            leanh::lean_dec(v___x_6163_);
                            v___x_6213_ = leanh::lean_box(0);
                            v_isShared_6214_ = v_isSharedCheck_6218_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6164_) == 1 {
                    v_val_6168_ = leanh::lean_ctor_get(v_a_6164_, 0);
                    v_isSharedCheck_6205_ = (!leanh::lean_is_exclusive(v_a_6164_)) as u8;
                    if v_isSharedCheck_6205_ == 0 {
                        v___x_6170_ = v_a_6164_;
                        v_isShared_6171_ = v_isSharedCheck_6205_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6168_);
                        leanh::lean_dec(v_a_6164_);
                        v___x_6170_ = leanh::lean_box(0);
                        v_isShared_6171_ = v_isSharedCheck_6205_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6164_);
                    v___x_6206_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_6167_ == 0 {
                        leanh::lean_ctor_set(v___x_6166_, 0, v___x_6206_);
                        v___x_6208_ = v___x_6166_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6209_, 0, v___x_6206_);
                        v___x_6208_ = v_reuseFailAlloc_6209_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6172_ = l_Lean_Expr_appArg_x21(v_e_6150_);
                v___x_6173_ = l_Lean_Meta_getCharValue_x3f(
                    v___x_6172_,
                    v_a_6151_,
                    v_a_6152_,
                    v_a_6153_,
                    v_a_6154_,
                );
                if leanh::lean_obj_tag(v___x_6173_) == 0 {
                    v_a_6174_ = leanh::lean_ctor_get(v___x_6173_, 0);
                    v_isSharedCheck_6196_ = (!leanh::lean_is_exclusive(v___x_6173_)) as u8;
                    if v_isSharedCheck_6196_ == 0 {
                        v___x_6176_ = v___x_6173_;
                        v_isShared_6177_ = v_isSharedCheck_6196_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6174_);
                        leanh::lean_dec(v___x_6173_);
                        v___x_6176_ = leanh::lean_box(0);
                        v_isShared_6177_ = v_isSharedCheck_6196_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6170_);
                    leanh::lean_dec(v_val_6168_);
                    leanh::lean_del_object(v___x_6166_);
                    v_a_6197_ = leanh::lean_ctor_get(v___x_6173_, 0);
                    v_isSharedCheck_6204_ = (!leanh::lean_is_exclusive(v___x_6173_)) as u8;
                    if v_isSharedCheck_6204_ == 0 {
                        v___x_6199_ = v___x_6173_;
                        v_isShared_6200_ = v_isSharedCheck_6204_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6197_);
                        leanh::lean_dec(v___x_6173_);
                        v___x_6199_ = leanh::lean_box(0);
                        v_isShared_6200_ = v_isSharedCheck_6204_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_6174_) == 1 {
                    leanh::lean_del_object(v___x_6166_);
                    v_val_6186_ = leanh::lean_ctor_get(v_a_6174_, 0);
                    leanh::lean_inc(v_val_6186_);
                    leanh::lean_dec_ref_known(v_a_6174_, 1);
                    v___x_6187_ = leanh::lean_unbox_uint32(v_val_6168_);
                    leanh::lean_dec(v_val_6168_);
                    v___x_6188_ = leanh::lean_unbox_uint32(v_val_6186_);
                    leanh::lean_dec(v_val_6186_);
                    v___x_6189_ = lean_uint32_dec_eq(v___x_6187_, v___x_6188_);
                    if v___x_6189_ == 0 {
                        v___x_6190_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Char_reduceBoolPred___redArg___closed__3_once
                            ),
                            _init_l_Char_reduceBoolPred___redArg___closed__3,
                        );
                        v___y_6179_ = v___x_6190_;
                        state = 4;
                        continue;
                    } else {
                        v___x_6191_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Char_reduceBoolPred___redArg___closed__6_once
                            ),
                            _init_l_Char_reduceBoolPred___redArg___closed__6,
                        );
                        v___y_6179_ = v___x_6191_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6176_);
                    leanh::lean_dec(v_a_6174_);
                    leanh::lean_del_object(v___x_6170_);
                    leanh::lean_dec(v_val_6168_);
                    v___x_6192_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_6167_ == 0 {
                        leanh::lean_ctor_set(v___x_6166_, 0, v___x_6192_);
                        v___x_6194_ = v___x_6166_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6195_, 0, v___x_6192_);
                        v___x_6194_ = v_reuseFailAlloc_6195_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v___y_6179_);
                if v_isShared_6171_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6170_, 0);
                    leanh::lean_ctor_set(v___x_6170_, 0, v___y_6179_);
                    v___x_6181_ = v___x_6170_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6185_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6185_, 0, v___y_6179_);
                    v___x_6181_ = v_reuseFailAlloc_6185_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6177_ == 0 {
                    leanh::lean_ctor_set(v___x_6176_, 0, v___x_6181_);
                    v___x_6183_ = v___x_6176_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 0, v___x_6181_);
                    v___x_6183_ = v_reuseFailAlloc_6184_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6183_;
            }
            7 => {
                return v___x_6194_;
            }
            8 => {
                if v_isShared_6200_ == 0 {
                    v___x_6202_ = v___x_6199_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6203_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6203_, 0, v_a_6197_);
                    v___x_6202_ = v_reuseFailAlloc_6203_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6202_;
            }
            10 => {
                return v___x_6208_;
            }
            11 => {
                if v_isShared_6214_ == 0 {
                    v___x_6216_ = v___x_6213_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6217_, 0, v_a_6211_);
                    v___x_6216_ = v_reuseFailAlloc_6217_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceBEq___redArg___boxed(
    mut v_e_6219_: *mut leanh::LeanObject,
    mut v_a_6220_: *mut leanh::LeanObject,
    mut v_a_6221_: *mut leanh::LeanObject,
    mut v_a_6222_: *mut leanh::LeanObject,
    mut v_a_6223_: *mut leanh::LeanObject,
    mut v_a_6224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6225_ = l_Char_reduceBEq___redArg(v_e_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_);
    leanh::lean_dec(v_a_6223_);
    leanh::lean_dec_ref(v_a_6222_);
    leanh::lean_dec(v_a_6221_);
    leanh::lean_dec_ref(v_a_6220_);
    leanh::lean_dec_ref(v_e_6219_);
    return v_res_6225_;
}
pub unsafe fn l_Char_reduceBEq(
    mut v_e_6226_: *mut leanh::LeanObject,
    mut v_a_6227_: *mut leanh::LeanObject,
    mut v_a_6228_: *mut leanh::LeanObject,
    mut v_a_6229_: *mut leanh::LeanObject,
    mut v_a_6230_: *mut leanh::LeanObject,
    mut v_a_6231_: *mut leanh::LeanObject,
    mut v_a_6232_: *mut leanh::LeanObject,
    mut v_a_6233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6235_ = l_Char_reduceBEq___redArg(v_e_6226_, v_a_6230_, v_a_6231_, v_a_6232_, v_a_6233_);
    return v___x_6235_;
}
pub unsafe fn l_Char_reduceBEq___boxed(
    mut v_e_6236_: *mut leanh::LeanObject,
    mut v_a_6237_: *mut leanh::LeanObject,
    mut v_a_6238_: *mut leanh::LeanObject,
    mut v_a_6239_: *mut leanh::LeanObject,
    mut v_a_6240_: *mut leanh::LeanObject,
    mut v_a_6241_: *mut leanh::LeanObject,
    mut v_a_6242_: *mut leanh::LeanObject,
    mut v_a_6243_: *mut leanh::LeanObject,
    mut v_a_6244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6245_ = l_Char_reduceBEq(
        v_e_6236_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_, v_a_6241_, v_a_6242_, v_a_6243_,
    );
    leanh::lean_dec(v_a_6243_);
    leanh::lean_dec_ref(v_a_6242_);
    leanh::lean_dec(v_a_6241_);
    leanh::lean_dec_ref(v_a_6240_);
    leanh::lean_dec(v_a_6239_);
    leanh::lean_dec_ref(v_a_6238_);
    leanh::lean_dec(v_a_6237_);
    leanh::lean_dec_ref(v_e_6236_);
    return v_res_6245_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6264_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_;
    v___x_6265_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_;
    v___x_6266_ =
        leanh::lean_alloc_closure(l_Char_reduceBEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_6267_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_6264_, v___x_6265_, v___x_6266_);
    return v___x_6267_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20____boxed(
    mut v_a_6268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6269_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_();
    return v_res_6269_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6270_ =
        leanh::lean_alloc_closure(l_Char_reduceBEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_6271_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6271_, 0, v___x_6270_);
    return v___x_6271_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: u8 = 0;
    let mut v___x_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6273_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_;
    v___x_6274_ = 1;
    v___x_6275_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_);
    v___x_6276_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_6273_, v___x_6274_, v___x_6275_);
    return v___x_6276_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22____boxed(
    mut v_a_6277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6278_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_();
    return v_res_6278_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: u8 = 0;
    let mut v___x_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6280_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_;
    v___x_6281_ = 1;
    v___x_6282_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_);
    v___x_6283_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_6280_, v___x_6281_, v___x_6282_);
    return v___x_6283_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24____boxed(
    mut v_a_6284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6285_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24_();
    return v_res_6285_;
}
pub unsafe fn l_Char_reduceBNe___redArg(
    mut v_e_6289_: *mut leanh::LeanObject,
    mut v_a_6290_: *mut leanh::LeanObject,
    mut v_a_6291_: *mut leanh::LeanObject,
    mut v_a_6292_: *mut leanh::LeanObject,
    mut v_a_6293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: u8 = 0;
    let mut v___x_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v_val_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6310_: u8 = 0;
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6316_: u8 = 0;
    let mut v___y_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: u32 = 0;
    let mut v___x_6329_: u32 = 0;
    let mut v___x_6330_: u8 = 0;
    let mut v___x_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6336_: u8 = 0;
    let mut v_a_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6340_: u8 = 0;
    let mut v___x_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6344_: u8 = 0;
    let mut v_isSharedCheck_6345_: u8 = 0;
    let mut v___x_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6350_: u8 = 0;
    let mut v_a_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6354_: u8 = 0;
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6295_ = l_Char_reduceBNe___redArg___closed__1;
                v___x_6296_ = leanh::lean_unsigned_to_nat(4);
                v___x_6297_ = l_Lean_Expr_isAppOfArity(v_e_6289_, v___x_6295_, v___x_6296_);
                if v___x_6297_ == 0 {
                    v___x_6298_ = l_Char_reduceUnary___redArg___closed__0;
                    v___x_6299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6299_, 0, v___x_6298_);
                    return v___x_6299_;
                } else {
                    v___x_6300_ = l_Lean_Expr_appFn_x21(v_e_6289_);
                    v___x_6301_ = l_Lean_Expr_appArg_x21(v___x_6300_);
                    leanh::lean_dec_ref(v___x_6300_);
                    v___x_6302_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_6301_,
                        v_a_6290_,
                        v_a_6291_,
                        v_a_6292_,
                        v_a_6293_,
                    );
                    if leanh::lean_obj_tag(v___x_6302_) == 0 {
                        v_a_6303_ = leanh::lean_ctor_get(v___x_6302_, 0);
                        v_isSharedCheck_6350_ =
                            (!leanh::lean_is_exclusive(v___x_6302_)) as u8;
                        if v_isSharedCheck_6350_ == 0 {
                            v___x_6305_ = v___x_6302_;
                            v_isShared_6306_ = v_isSharedCheck_6350_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6303_);
                            leanh::lean_dec(v___x_6302_);
                            v___x_6305_ = leanh::lean_box(0);
                            v_isShared_6306_ = v_isSharedCheck_6350_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6351_ = leanh::lean_ctor_get(v___x_6302_, 0);
                        v_isSharedCheck_6358_ =
                            (!leanh::lean_is_exclusive(v___x_6302_)) as u8;
                        if v_isSharedCheck_6358_ == 0 {
                            v___x_6353_ = v___x_6302_;
                            v_isShared_6354_ = v_isSharedCheck_6358_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6351_);
                            leanh::lean_dec(v___x_6302_);
                            v___x_6353_ = leanh::lean_box(0);
                            v_isShared_6354_ = v_isSharedCheck_6358_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6303_) == 1 {
                    v_val_6307_ = leanh::lean_ctor_get(v_a_6303_, 0);
                    v_isSharedCheck_6345_ = (!leanh::lean_is_exclusive(v_a_6303_)) as u8;
                    if v_isSharedCheck_6345_ == 0 {
                        v___x_6309_ = v_a_6303_;
                        v_isShared_6310_ = v_isSharedCheck_6345_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6307_);
                        leanh::lean_dec(v_a_6303_);
                        v___x_6309_ = leanh::lean_box(0);
                        v_isShared_6310_ = v_isSharedCheck_6345_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6303_);
                    v___x_6346_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_6306_ == 0 {
                        leanh::lean_ctor_set(v___x_6305_, 0, v___x_6346_);
                        v___x_6348_ = v___x_6305_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6349_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6349_, 0, v___x_6346_);
                        v___x_6348_ = v_reuseFailAlloc_6349_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6311_ = l_Lean_Expr_appArg_x21(v_e_6289_);
                v___x_6312_ = l_Lean_Meta_getCharValue_x3f(
                    v___x_6311_,
                    v_a_6290_,
                    v_a_6291_,
                    v_a_6292_,
                    v_a_6293_,
                );
                if leanh::lean_obj_tag(v___x_6312_) == 0 {
                    v_a_6313_ = leanh::lean_ctor_get(v___x_6312_, 0);
                    v_isSharedCheck_6336_ = (!leanh::lean_is_exclusive(v___x_6312_)) as u8;
                    if v_isSharedCheck_6336_ == 0 {
                        v___x_6315_ = v___x_6312_;
                        v_isShared_6316_ = v_isSharedCheck_6336_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6313_);
                        leanh::lean_dec(v___x_6312_);
                        v___x_6315_ = leanh::lean_box(0);
                        v_isShared_6316_ = v_isSharedCheck_6336_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6309_);
                    leanh::lean_dec(v_val_6307_);
                    leanh::lean_del_object(v___x_6305_);
                    v_a_6337_ = leanh::lean_ctor_get(v___x_6312_, 0);
                    v_isSharedCheck_6344_ = (!leanh::lean_is_exclusive(v___x_6312_)) as u8;
                    if v_isSharedCheck_6344_ == 0 {
                        v___x_6339_ = v___x_6312_;
                        v_isShared_6340_ = v_isSharedCheck_6344_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6337_);
                        leanh::lean_dec(v___x_6312_);
                        v___x_6339_ = leanh::lean_box(0);
                        v_isShared_6340_ = v_isSharedCheck_6344_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_6313_) == 1 {
                    leanh::lean_del_object(v___x_6305_);
                    v_val_6327_ = leanh::lean_ctor_get(v_a_6313_, 0);
                    leanh::lean_inc(v_val_6327_);
                    leanh::lean_dec_ref_known(v_a_6313_, 1);
                    v___x_6328_ = leanh::lean_unbox_uint32(v_val_6307_);
                    leanh::lean_dec(v_val_6307_);
                    v___x_6329_ = leanh::lean_unbox_uint32(v_val_6327_);
                    leanh::lean_dec(v_val_6327_);
                    v___x_6330_ = lean_uint32_dec_eq(v___x_6328_, v___x_6329_);
                    if v___x_6330_ == 0 {
                        if v___x_6297_ == 0 {
                            state = 7;
                            continue;
                        } else {
                            v___x_6331_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__6),
                                core::ptr::addr_of_mut!(
                                    l_Char_reduceBoolPred___redArg___closed__6_once
                                ),
                                _init_l_Char_reduceBoolPred___redArg___closed__6,
                            );
                            v___y_6318_ = v___x_6331_;
                            state = 4;
                            continue;
                        }
                    } else {
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6315_);
                    leanh::lean_dec(v_a_6313_);
                    leanh::lean_del_object(v___x_6309_);
                    leanh::lean_dec(v_val_6307_);
                    v___x_6332_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_6306_ == 0 {
                        leanh::lean_ctor_set(v___x_6305_, 0, v___x_6332_);
                        v___x_6334_ = v___x_6305_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6335_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6335_, 0, v___x_6332_);
                        v___x_6334_ = v_reuseFailAlloc_6335_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v___y_6318_);
                if v_isShared_6310_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6309_, 0);
                    leanh::lean_ctor_set(v___x_6309_, 0, v___y_6318_);
                    v___x_6320_ = v___x_6309_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6324_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6324_, 0, v___y_6318_);
                    v___x_6320_ = v_reuseFailAlloc_6324_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6316_ == 0 {
                    leanh::lean_ctor_set(v___x_6315_, 0, v___x_6320_);
                    v___x_6322_ = v___x_6315_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6323_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6323_, 0, v___x_6320_);
                    v___x_6322_ = v_reuseFailAlloc_6323_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6322_;
            }
            7 => {
                v___x_6326_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Char_reduceBoolPred___redArg___closed__3_once),
                    _init_l_Char_reduceBoolPred___redArg___closed__3,
                );
                v___y_6318_ = v___x_6326_;
                state = 4;
                continue;
            }
            8 => {
                return v___x_6334_;
            }
            9 => {
                if v_isShared_6340_ == 0 {
                    v___x_6342_ = v___x_6339_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6343_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6343_, 0, v_a_6337_);
                    v___x_6342_ = v_reuseFailAlloc_6343_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6342_;
            }
            11 => {
                return v___x_6348_;
            }
            12 => {
                if v_isShared_6354_ == 0 {
                    v___x_6356_ = v___x_6353_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6357_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_a_6351_);
                    v___x_6356_ = v_reuseFailAlloc_6357_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceBNe___redArg___boxed(
    mut v_e_6359_: *mut leanh::LeanObject,
    mut v_a_6360_: *mut leanh::LeanObject,
    mut v_a_6361_: *mut leanh::LeanObject,
    mut v_a_6362_: *mut leanh::LeanObject,
    mut v_a_6363_: *mut leanh::LeanObject,
    mut v_a_6364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6365_ = l_Char_reduceBNe___redArg(v_e_6359_, v_a_6360_, v_a_6361_, v_a_6362_, v_a_6363_);
    leanh::lean_dec(v_a_6363_);
    leanh::lean_dec_ref(v_a_6362_);
    leanh::lean_dec(v_a_6361_);
    leanh::lean_dec_ref(v_a_6360_);
    leanh::lean_dec_ref(v_e_6359_);
    return v_res_6365_;
}
pub unsafe fn l_Char_reduceBNe(
    mut v_e_6366_: *mut leanh::LeanObject,
    mut v_a_6367_: *mut leanh::LeanObject,
    mut v_a_6368_: *mut leanh::LeanObject,
    mut v_a_6369_: *mut leanh::LeanObject,
    mut v_a_6370_: *mut leanh::LeanObject,
    mut v_a_6371_: *mut leanh::LeanObject,
    mut v_a_6372_: *mut leanh::LeanObject,
    mut v_a_6373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6375_ = l_Char_reduceBNe___redArg(v_e_6366_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_);
    return v___x_6375_;
}
pub unsafe fn l_Char_reduceBNe___boxed(
    mut v_e_6376_: *mut leanh::LeanObject,
    mut v_a_6377_: *mut leanh::LeanObject,
    mut v_a_6378_: *mut leanh::LeanObject,
    mut v_a_6379_: *mut leanh::LeanObject,
    mut v_a_6380_: *mut leanh::LeanObject,
    mut v_a_6381_: *mut leanh::LeanObject,
    mut v_a_6382_: *mut leanh::LeanObject,
    mut v_a_6383_: *mut leanh::LeanObject,
    mut v_a_6384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6385_ = l_Char_reduceBNe(
        v_e_6376_, v_a_6377_, v_a_6378_, v_a_6379_, v_a_6380_, v_a_6381_, v_a_6382_, v_a_6383_,
    );
    leanh::lean_dec(v_a_6383_);
    leanh::lean_dec_ref(v_a_6382_);
    leanh::lean_dec(v_a_6381_);
    leanh::lean_dec_ref(v_a_6380_);
    leanh::lean_dec(v_a_6379_);
    leanh::lean_dec_ref(v_a_6378_);
    leanh::lean_dec(v_a_6377_);
    leanh::lean_dec_ref(v_e_6376_);
    return v_res_6385_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_()
-> *mut leanh::LeanObject {
    let mut v___x_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6404_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_;
    v___x_6405_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_;
    v___x_6406_ =
        leanh::lean_alloc_closure(l_Char_reduceBNe___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_6407_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_6404_, v___x_6405_, v___x_6406_);
    return v___x_6407_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20____boxed(
    mut v_a_6408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6409_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_();
    return v_res_6409_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6410_ =
        leanh::lean_alloc_closure(l_Char_reduceBNe___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_6411_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6411_, 0, v___x_6410_);
    return v___x_6411_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_()
-> *mut leanh::LeanObject {
    let mut v___x_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: u8 = 0;
    let mut v___x_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6413_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_;
    v___x_6414_ = 1;
    v___x_6415_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_);
    v___x_6416_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_6413_, v___x_6414_, v___x_6415_);
    return v___x_6416_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22____boxed(
    mut v_a_6417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6418_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_();
    return v_res_6418_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24_()
-> *mut leanh::LeanObject {
    let mut v___x_6420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: u8 = 0;
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6420_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_;
    v___x_6421_ = 1;
    v___x_6422_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_);
    v___x_6423_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_6420_, v___x_6421_, v___x_6422_);
    return v___x_6423_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24____boxed(
    mut v_a_6424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6425_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24_();
    return v_res_6425_;
}
pub unsafe fn l_Char_isValue___redArg(
    mut v_e_6426_: *mut leanh::LeanObject,
    mut v_a_6427_: *mut leanh::LeanObject,
    mut v_a_6428_: *mut leanh::LeanObject,
    mut v_a_6429_: *mut leanh::LeanObject,
    mut v_a_6430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6436_: u8 = 0;
    let mut v___x_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6443_: u8 = 0;
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6450_: u8 = 0;
    let mut v_unused_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6452_: u8 = 0;
    let mut v_a_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6456_: u8 = 0;
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_6426_);
                v___x_6432_ = l_Lean_Meta_getCharValue_x3f(
                    v_e_6426_, v_a_6427_, v_a_6428_, v_a_6429_, v_a_6430_,
                );
                if leanh::lean_obj_tag(v___x_6432_) == 0 {
                    v_a_6433_ = leanh::lean_ctor_get(v___x_6432_, 0);
                    v_isSharedCheck_6452_ = (!leanh::lean_is_exclusive(v___x_6432_)) as u8;
                    if v_isSharedCheck_6452_ == 0 {
                        v___x_6435_ = v___x_6432_;
                        v_isShared_6436_ = v_isSharedCheck_6452_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6433_);
                        leanh::lean_dec(v___x_6432_);
                        v___x_6435_ = leanh::lean_box(0);
                        v_isShared_6436_ = v_isSharedCheck_6452_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6426_);
                    v_a_6453_ = leanh::lean_ctor_get(v___x_6432_, 0);
                    v_isSharedCheck_6460_ = (!leanh::lean_is_exclusive(v___x_6432_)) as u8;
                    if v_isSharedCheck_6460_ == 0 {
                        v___x_6455_ = v___x_6432_;
                        v_isShared_6456_ = v_isSharedCheck_6460_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6453_);
                        leanh::lean_dec(v___x_6432_);
                        v___x_6455_ = leanh::lean_box(0);
                        v_isShared_6456_ = v_isSharedCheck_6460_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6433_) == 0 {
                    leanh::lean_dec_ref(v_e_6426_);
                    v___x_6437_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_6436_ == 0 {
                        leanh::lean_ctor_set(v___x_6435_, 0, v___x_6437_);
                        v___x_6439_ = v___x_6435_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6440_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6440_, 0, v___x_6437_);
                        v___x_6439_ = v_reuseFailAlloc_6440_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_6450_ = (!leanh::lean_is_exclusive(v_a_6433_)) as u8;
                    if v_isSharedCheck_6450_ == 0 {
                        v_unused_6451_ = leanh::lean_ctor_get(v_a_6433_, 0);
                        leanh::lean_dec(v_unused_6451_);
                        v___x_6442_ = v_a_6433_;
                        v_isShared_6443_ = v_isSharedCheck_6450_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_6433_);
                        v___x_6442_ = leanh::lean_box(0);
                        v_isShared_6443_ = v_isSharedCheck_6450_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6439_;
            }
            3 => {
                if v_isShared_6443_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6442_, 0);
                    leanh::lean_ctor_set(v___x_6442_, 0, v_e_6426_);
                    v___x_6445_ = v___x_6442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6449_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_e_6426_);
                    v___x_6445_ = v_reuseFailAlloc_6449_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6436_ == 0 {
                    leanh::lean_ctor_set(v___x_6435_, 0, v___x_6445_);
                    v___x_6447_ = v___x_6435_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6448_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6448_, 0, v___x_6445_);
                    v___x_6447_ = v_reuseFailAlloc_6448_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6447_;
            }
            6 => {
                if v_isShared_6456_ == 0 {
                    v___x_6458_ = v___x_6455_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
                    v___x_6458_ = v_reuseFailAlloc_6459_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6458_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_isValue___redArg___boxed(
    mut v_e_6461_: *mut leanh::LeanObject,
    mut v_a_6462_: *mut leanh::LeanObject,
    mut v_a_6463_: *mut leanh::LeanObject,
    mut v_a_6464_: *mut leanh::LeanObject,
    mut v_a_6465_: *mut leanh::LeanObject,
    mut v_a_6466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6467_ = l_Char_isValue___redArg(v_e_6461_, v_a_6462_, v_a_6463_, v_a_6464_, v_a_6465_);
    leanh::lean_dec(v_a_6465_);
    leanh::lean_dec_ref(v_a_6464_);
    leanh::lean_dec(v_a_6463_);
    leanh::lean_dec_ref(v_a_6462_);
    return v_res_6467_;
}
pub unsafe fn l_Char_isValue(
    mut v_e_6468_: *mut leanh::LeanObject,
    mut v_a_6469_: *mut leanh::LeanObject,
    mut v_a_6470_: *mut leanh::LeanObject,
    mut v_a_6471_: *mut leanh::LeanObject,
    mut v_a_6472_: *mut leanh::LeanObject,
    mut v_a_6473_: *mut leanh::LeanObject,
    mut v_a_6474_: *mut leanh::LeanObject,
    mut v_a_6475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6477_ = l_Char_isValue___redArg(v_e_6468_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_);
    return v___x_6477_;
}
pub unsafe fn l_Char_isValue___boxed(
    mut v_e_6478_: *mut leanh::LeanObject,
    mut v_a_6479_: *mut leanh::LeanObject,
    mut v_a_6480_: *mut leanh::LeanObject,
    mut v_a_6481_: *mut leanh::LeanObject,
    mut v_a_6482_: *mut leanh::LeanObject,
    mut v_a_6483_: *mut leanh::LeanObject,
    mut v_a_6484_: *mut leanh::LeanObject,
    mut v_a_6485_: *mut leanh::LeanObject,
    mut v_a_6486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6487_ = l_Char_isValue(
        v_e_6478_, v_a_6479_, v_a_6480_, v_a_6481_, v_a_6482_, v_a_6483_, v_a_6484_, v_a_6485_,
    );
    leanh::lean_dec(v_a_6485_);
    leanh::lean_dec_ref(v_a_6484_);
    leanh::lean_dec(v_a_6483_);
    leanh::lean_dec_ref(v_a_6482_);
    leanh::lean_dec(v_a_6481_);
    leanh::lean_dec_ref(v_a_6480_);
    leanh::lean_dec(v_a_6479_);
    return v_res_6487_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6502_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_;
    v___x_6503_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_;
    v___x_6504_ =
        leanh::lean_alloc_closure(l_Char_isValue___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_6505_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_6502_, v___x_6503_, v___x_6504_);
    return v___x_6505_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13____boxed(
    mut v_a_6506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6507_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_();
    return v_res_6507_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6508_ =
        leanh::lean_alloc_closure(l_Char_isValue___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_6509_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6509_, 0, v___x_6508_);
    return v___x_6509_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: u8 = 0;
    let mut v___x_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6511_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_;
    v___x_6512_ = 0;
    v___x_6513_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_);
    v___x_6514_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_6511_, v___x_6512_, v___x_6513_);
    return v___x_6514_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15____boxed(
    mut v_a_6515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6516_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_();
    return v_res_6516_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: u8 = 0;
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6518_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_;
    v___x_6519_ = 0;
    v___x_6520_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_);
    v___x_6521_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_6518_, v___x_6519_, v___x_6520_);
    return v___x_6521_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17____boxed(
    mut v_a_6522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6523_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17_();
    return v_res_6523_;
}
pub unsafe fn l_Char_reduceOfNatAux___redArg(
    mut v_e_6528_: *mut leanh::LeanObject,
    mut v_a_6529_: *mut leanh::LeanObject,
    mut v_a_6530_: *mut leanh::LeanObject,
    mut v_a_6531_: *mut leanh::LeanObject,
    mut v_a_6532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6538_: u8 = 0;
    let mut v___x_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: u8 = 0;
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: u8 = 0;
    let mut v_arg_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: u8 = 0;
    let mut v___x_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6556_: u8 = 0;
    let mut v_val_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6560_: u8 = 0;
    let mut v___x_6561_: u32 = 0;
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6572_: u8 = 0;
    let mut v___x_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6577_: u8 = 0;
    let mut v_a_6578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6581_: u8 = 0;
    let mut v___x_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6585_: u8 = 0;
    let mut v_isSharedCheck_6586_: u8 = 0;
    let mut v_a_6587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6590_: u8 = 0;
    let mut v___x_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6534_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_6528_, v_a_6530_);
                if leanh::lean_obj_tag(v___x_6534_) == 0 {
                    v_a_6535_ = leanh::lean_ctor_get(v___x_6534_, 0);
                    v_isSharedCheck_6586_ = (!leanh::lean_is_exclusive(v___x_6534_)) as u8;
                    if v_isSharedCheck_6586_ == 0 {
                        v___x_6537_ = v___x_6534_;
                        v_isShared_6538_ = v_isSharedCheck_6586_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6535_);
                        leanh::lean_dec(v___x_6534_);
                        v___x_6537_ = leanh::lean_box(0);
                        v_isShared_6538_ = v_isSharedCheck_6586_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6587_ = leanh::lean_ctor_get(v___x_6534_, 0);
                    v_isSharedCheck_6594_ = (!leanh::lean_is_exclusive(v___x_6534_)) as u8;
                    if v_isSharedCheck_6594_ == 0 {
                        v___x_6589_ = v___x_6534_;
                        v_isShared_6590_ = v_isSharedCheck_6594_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6587_);
                        leanh::lean_dec(v___x_6534_);
                        v___x_6589_ = leanh::lean_box(0);
                        v_isShared_6590_ = v_isSharedCheck_6594_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6544_ = l_Lean_Expr_cleanupAnnotations(v_a_6535_);
                v___x_6545_ = l_Lean_Expr_isApp(v___x_6544_);
                if v___x_6545_ == 0 {
                    leanh::lean_dec_ref(v___x_6544_);
                    state = 2;
                    continue;
                } else {
                    v___x_6546_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6544_);
                    v___x_6547_ = l_Lean_Expr_isApp(v___x_6546_);
                    if v___x_6547_ == 0 {
                        leanh::lean_dec_ref(v___x_6546_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_6548_ = leanh::lean_ctor_get(v___x_6546_, 1);
                        leanh::lean_inc_ref(v_arg_6548_);
                        v___x_6549_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6546_);
                        v___x_6550_ = l_Char_reduceOfNatAux___redArg___closed__1;
                        v___x_6551_ = l_Lean_Expr_isConstOf(v___x_6549_, v___x_6550_);
                        leanh::lean_dec_ref(v___x_6549_);
                        if v___x_6551_ == 0 {
                            leanh::lean_dec_ref(v_arg_6548_);
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_6537_);
                            v___x_6552_ = l_Lean_Meta_getNatValue_x3f(
                                v_arg_6548_,
                                v_a_6529_,
                                v_a_6530_,
                                v_a_6531_,
                                v_a_6532_,
                            );
                            leanh::lean_dec_ref(v_arg_6548_);
                            if leanh::lean_obj_tag(v___x_6552_) == 0 {
                                v_a_6553_ = leanh::lean_ctor_get(v___x_6552_, 0);
                                v_isSharedCheck_6577_ =
                                    (!leanh::lean_is_exclusive(v___x_6552_)) as u8;
                                if v_isSharedCheck_6577_ == 0 {
                                    v___x_6555_ = v___x_6552_;
                                    v_isShared_6556_ = v_isSharedCheck_6577_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6553_);
                                    leanh::lean_dec(v___x_6552_);
                                    v___x_6555_ = leanh::lean_box(0);
                                    v_isShared_6556_ = v_isSharedCheck_6577_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_a_6578_ = leanh::lean_ctor_get(v___x_6552_, 0);
                                v_isSharedCheck_6585_ =
                                    (!leanh::lean_is_exclusive(v___x_6552_)) as u8;
                                if v_isSharedCheck_6585_ == 0 {
                                    v___x_6580_ = v___x_6552_;
                                    v_isShared_6581_ = v_isSharedCheck_6585_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6578_);
                                    leanh::lean_dec(v___x_6552_);
                                    v___x_6580_ = leanh::lean_box(0);
                                    v_isShared_6581_ = v_isSharedCheck_6585_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_6540_ = l_Char_reduceUnary___redArg___closed__0;
                if v_isShared_6538_ == 0 {
                    leanh::lean_ctor_set(v___x_6537_, 0, v___x_6540_);
                    v___x_6542_ = v___x_6537_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6543_, 0, v___x_6540_);
                    v___x_6542_ = v_reuseFailAlloc_6543_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6542_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_6553_) == 1 {
                    v_val_6557_ = leanh::lean_ctor_get(v_a_6553_, 0);
                    v_isSharedCheck_6572_ = (!leanh::lean_is_exclusive(v_a_6553_)) as u8;
                    if v_isSharedCheck_6572_ == 0 {
                        v___x_6559_ = v_a_6553_;
                        v_isShared_6560_ = v_isSharedCheck_6572_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6557_);
                        leanh::lean_dec(v_a_6553_);
                        v___x_6559_ = leanh::lean_box(0);
                        v_isShared_6560_ = v_isSharedCheck_6572_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6553_);
                    v___x_6573_ = l_Char_reduceUnary___redArg___closed__0;
                    if v_isShared_6556_ == 0 {
                        leanh::lean_ctor_set(v___x_6555_, 0, v___x_6573_);
                        v___x_6575_ = v___x_6555_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6576_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6576_, 0, v___x_6573_);
                        v___x_6575_ = v_reuseFailAlloc_6576_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6561_ = l_Char_ofNat(v_val_6557_);
                leanh::lean_dec(v_val_6557_);
                v___x_6562_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_reduceToLower___redArg___closed__5),
                    core::ptr::addr_of_mut!(l_Char_reduceToLower___redArg___closed__5_once),
                    _init_l_Char_reduceToLower___redArg___closed__5,
                );
                v___x_6563_ = lean_uint32_to_nat(v___x_6561_);
                v___x_6564_ = l_Lean_mkRawNatLit(v___x_6563_);
                v___x_6565_ = l_Lean_Expr_app___override(v___x_6562_, v___x_6564_);
                if v_isShared_6560_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6559_, 0);
                    leanh::lean_ctor_set(v___x_6559_, 0, v___x_6565_);
                    v___x_6567_ = v___x_6559_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6571_, 0, v___x_6565_);
                    v___x_6567_ = v_reuseFailAlloc_6571_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6556_ == 0 {
                    leanh::lean_ctor_set(v___x_6555_, 0, v___x_6567_);
                    v___x_6569_ = v___x_6555_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6570_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6570_, 0, v___x_6567_);
                    v___x_6569_ = v_reuseFailAlloc_6570_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6569_;
            }
            8 => {
                return v___x_6575_;
            }
            9 => {
                if v_isShared_6581_ == 0 {
                    v___x_6583_ = v___x_6580_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6584_, 0, v_a_6578_);
                    v___x_6583_ = v_reuseFailAlloc_6584_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6583_;
            }
            11 => {
                if v_isShared_6590_ == 0 {
                    v___x_6592_ = v___x_6589_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6587_);
                    v___x_6592_ = v_reuseFailAlloc_6593_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceOfNatAux___redArg___boxed(
    mut v_e_6595_: *mut leanh::LeanObject,
    mut v_a_6596_: *mut leanh::LeanObject,
    mut v_a_6597_: *mut leanh::LeanObject,
    mut v_a_6598_: *mut leanh::LeanObject,
    mut v_a_6599_: *mut leanh::LeanObject,
    mut v_a_6600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6601_ =
        l_Char_reduceOfNatAux___redArg(v_e_6595_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_);
    leanh::lean_dec(v_a_6599_);
    leanh::lean_dec_ref(v_a_6598_);
    leanh::lean_dec(v_a_6597_);
    leanh::lean_dec_ref(v_a_6596_);
    return v_res_6601_;
}
pub unsafe fn l_Char_reduceOfNatAux(
    mut v_e_6602_: *mut leanh::LeanObject,
    mut v_a_6603_: *mut leanh::LeanObject,
    mut v_a_6604_: *mut leanh::LeanObject,
    mut v_a_6605_: *mut leanh::LeanObject,
    mut v_a_6606_: *mut leanh::LeanObject,
    mut v_a_6607_: *mut leanh::LeanObject,
    mut v_a_6608_: *mut leanh::LeanObject,
    mut v_a_6609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6611_ =
        l_Char_reduceOfNatAux___redArg(v_e_6602_, v_a_6606_, v_a_6607_, v_a_6608_, v_a_6609_);
    return v___x_6611_;
}
pub unsafe fn l_Char_reduceOfNatAux___boxed(
    mut v_e_6612_: *mut leanh::LeanObject,
    mut v_a_6613_: *mut leanh::LeanObject,
    mut v_a_6614_: *mut leanh::LeanObject,
    mut v_a_6615_: *mut leanh::LeanObject,
    mut v_a_6616_: *mut leanh::LeanObject,
    mut v_a_6617_: *mut leanh::LeanObject,
    mut v_a_6618_: *mut leanh::LeanObject,
    mut v_a_6619_: *mut leanh::LeanObject,
    mut v_a_6620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6621_ = l_Char_reduceOfNatAux(
        v_e_6612_, v_a_6613_, v_a_6614_, v_a_6615_, v_a_6616_, v_a_6617_, v_a_6618_, v_a_6619_,
    );
    leanh::lean_dec(v_a_6619_);
    leanh::lean_dec_ref(v_a_6618_);
    leanh::lean_dec(v_a_6617_);
    leanh::lean_dec_ref(v_a_6616_);
    leanh::lean_dec(v_a_6615_);
    leanh::lean_dec_ref(v_a_6614_);
    leanh::lean_dec(v_a_6613_);
    return v_res_6621_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_()
-> *mut leanh::LeanObject {
    let mut v___x_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6637_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_;
    v___x_6638_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_;
    v___x_6639_ = leanh::lean_alloc_closure(
        l_Char_reduceOfNatAux___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6640_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_6637_, v___x_6638_, v___x_6639_);
    return v___x_6640_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14____boxed(
    mut v_a_6641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6642_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_();
    return v_res_6642_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_()
-> *mut leanh::LeanObject {
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6643_ = leanh::lean_alloc_closure(
        l_Char_reduceOfNatAux___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6644_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6644_, 0, v___x_6643_);
    return v___x_6644_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_()
-> *mut leanh::LeanObject {
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: u8 = 0;
    let mut v___x_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6646_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_;
    v___x_6647_ = 1;
    v___x_6648_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_);
    v___x_6649_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_6646_, v___x_6647_, v___x_6648_);
    return v___x_6649_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16____boxed(
    mut v_a_6650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6651_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_();
    return v_res_6651_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18_()
-> *mut leanh::LeanObject {
    let mut v___x_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: u8 = 0;
    let mut v___x_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6653_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_;
    v___x_6654_ = 1;
    v___x_6655_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_);
    v___x_6656_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_6653_, v___x_6654_, v___x_6655_);
    return v___x_6656_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18____boxed(
    mut v_a_6657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6658_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18_();
    return v_res_6658_;
}
pub unsafe fn _init_l_Char_reduceDefault___redArg___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_6664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6664_ = leanh::lean_unsigned_to_nat(65);
    v___x_6665_ = l_Lean_mkRawNatLit(v___x_6664_);
    return v___x_6665_;
}
pub unsafe fn _init_l_Char_reduceDefault___redArg___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_6666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6666_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_reduceDefault___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Char_reduceDefault___redArg___closed__3_once),
        _init_l_Char_reduceDefault___redArg___closed__3,
    );
    v___x_6667_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_reduceToLower___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Char_reduceToLower___redArg___closed__5_once),
        _init_l_Char_reduceToLower___redArg___closed__5,
    );
    v___x_6668_ = l_Lean_Expr_app___override(v___x_6667_, v___x_6666_);
    return v___x_6668_;
}
pub unsafe fn _init_l_Char_reduceDefault___redArg___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6669_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_reduceDefault___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Char_reduceDefault___redArg___closed__4_once),
        _init_l_Char_reduceDefault___redArg___closed__4,
    );
    v___x_6670_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6670_, 0, v___x_6669_);
    return v___x_6670_;
}
pub unsafe fn l_Char_reduceDefault___redArg(
    mut v_e_6671_: *mut leanh::LeanObject,
    mut v_a_6672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6678_: u8 = 0;
    let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: u8 = 0;
    let mut v___x_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: u8 = 0;
    let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: u8 = 0;
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6693_: u8 = 0;
    let mut v_a_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6697_: u8 = 0;
    let mut v___x_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6674_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_6671_, v_a_6672_);
                if leanh::lean_obj_tag(v___x_6674_) == 0 {
                    v_a_6675_ = leanh::lean_ctor_get(v___x_6674_, 0);
                    v_isSharedCheck_6693_ = (!leanh::lean_is_exclusive(v___x_6674_)) as u8;
                    if v_isSharedCheck_6693_ == 0 {
                        v___x_6677_ = v___x_6674_;
                        v_isShared_6678_ = v_isSharedCheck_6693_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6675_);
                        leanh::lean_dec(v___x_6674_);
                        v___x_6677_ = leanh::lean_box(0);
                        v_isShared_6678_ = v_isSharedCheck_6693_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6694_ = leanh::lean_ctor_get(v___x_6674_, 0);
                    v_isSharedCheck_6701_ = (!leanh::lean_is_exclusive(v___x_6674_)) as u8;
                    if v_isSharedCheck_6701_ == 0 {
                        v___x_6696_ = v___x_6674_;
                        v_isShared_6697_ = v_isSharedCheck_6701_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6694_);
                        leanh::lean_dec(v___x_6674_);
                        v___x_6696_ = leanh::lean_box(0);
                        v_isShared_6697_ = v_isSharedCheck_6701_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6684_ = l_Lean_Expr_cleanupAnnotations(v_a_6675_);
                v___x_6685_ = l_Lean_Expr_isApp(v___x_6684_);
                if v___x_6685_ == 0 {
                    leanh::lean_dec_ref(v___x_6684_);
                    state = 2;
                    continue;
                } else {
                    v___x_6686_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6684_);
                    v___x_6687_ = l_Lean_Expr_isApp(v___x_6686_);
                    if v___x_6687_ == 0 {
                        leanh::lean_dec_ref(v___x_6686_);
                        state = 2;
                        continue;
                    } else {
                        v___x_6688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6686_);
                        v___x_6689_ = l_Char_reduceDefault___redArg___closed__2;
                        v___x_6690_ = l_Lean_Expr_isConstOf(v___x_6688_, v___x_6689_);
                        leanh::lean_dec_ref(v___x_6688_);
                        if v___x_6690_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_6677_);
                            v___x_6691_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Char_reduceDefault___redArg___closed__5),
                                core::ptr::addr_of_mut!(
                                    l_Char_reduceDefault___redArg___closed__5_once
                                ),
                                _init_l_Char_reduceDefault___redArg___closed__5,
                            );
                            v___x_6692_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_6692_, 0, v___x_6691_);
                            return v___x_6692_;
                        }
                    }
                }
            }
            2 => {
                v___x_6680_ = l_Char_reduceUnary___redArg___closed__0;
                if v_isShared_6678_ == 0 {
                    leanh::lean_ctor_set(v___x_6677_, 0, v___x_6680_);
                    v___x_6682_ = v___x_6677_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6683_, 0, v___x_6680_);
                    v___x_6682_ = v_reuseFailAlloc_6683_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6682_;
            }
            4 => {
                if v_isShared_6697_ == 0 {
                    v___x_6699_ = v___x_6696_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6700_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6700_, 0, v_a_6694_);
                    v___x_6699_ = v_reuseFailAlloc_6700_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_reduceDefault___redArg___boxed(
    mut v_e_6702_: *mut leanh::LeanObject,
    mut v_a_6703_: *mut leanh::LeanObject,
    mut v_a_6704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6705_ = l_Char_reduceDefault___redArg(v_e_6702_, v_a_6703_);
    leanh::lean_dec(v_a_6703_);
    return v_res_6705_;
}
pub unsafe fn l_Char_reduceDefault(
    mut v_e_6706_: *mut leanh::LeanObject,
    mut v_a_6707_: *mut leanh::LeanObject,
    mut v_a_6708_: *mut leanh::LeanObject,
    mut v_a_6709_: *mut leanh::LeanObject,
    mut v_a_6710_: *mut leanh::LeanObject,
    mut v_a_6711_: *mut leanh::LeanObject,
    mut v_a_6712_: *mut leanh::LeanObject,
    mut v_a_6713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6715_ = l_Char_reduceDefault___redArg(v_e_6706_, v_a_6711_);
    return v___x_6715_;
}
pub unsafe fn l_Char_reduceDefault___boxed(
    mut v_e_6716_: *mut leanh::LeanObject,
    mut v_a_6717_: *mut leanh::LeanObject,
    mut v_a_6718_: *mut leanh::LeanObject,
    mut v_a_6719_: *mut leanh::LeanObject,
    mut v_a_6720_: *mut leanh::LeanObject,
    mut v_a_6721_: *mut leanh::LeanObject,
    mut v_a_6722_: *mut leanh::LeanObject,
    mut v_a_6723_: *mut leanh::LeanObject,
    mut v_a_6724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6725_ = l_Char_reduceDefault(
        v_e_6716_, v_a_6717_, v_a_6718_, v_a_6719_, v_a_6720_, v_a_6721_, v_a_6722_, v_a_6723_,
    );
    leanh::lean_dec(v_a_6723_);
    leanh::lean_dec_ref(v_a_6722_);
    leanh::lean_dec(v_a_6721_);
    leanh::lean_dec_ref(v_a_6720_);
    leanh::lean_dec(v_a_6719_);
    leanh::lean_dec_ref(v_a_6718_);
    leanh::lean_dec(v_a_6717_);
    return v_res_6725_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6742_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_;
    v___x_6743_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_;
    v___x_6744_ = leanh::lean_alloc_closure(
        l_Char_reduceDefault___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6745_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_6742_, v___x_6743_, v___x_6744_);
    return v___x_6745_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15____boxed(
    mut v_a_6746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6747_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_();
    return v_res_6747_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6748_ = leanh::lean_alloc_closure(
        l_Char_reduceDefault___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6749_, 0, v___x_6748_);
    return v___x_6749_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: u8 = 0;
    let mut v___x_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6751_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_;
    v___x_6752_ = 1;
    v___x_6753_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_);
    v___x_6754_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_6751_, v___x_6752_, v___x_6753_);
    return v___x_6754_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17____boxed(
    mut v_a_6755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6756_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_();
    return v_res_6756_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19_()
-> *mut leanh::LeanObject {
    let mut v___x_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: u8 = 0;
    let mut v___x_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6758_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_;
    v___x_6759_ = 1;
    v___x_6760_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_);
    v___x_6761_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_6758_, v___x_6759_, v___x_6760_);
    return v___x_6761_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19____boxed(
    mut v_a_6762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6763_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19_();
    return v_res_6763_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(
    mut v_a_6764_: u32,
    mut v_as_6765_: *mut leanh::LeanObject,
    mut v_i_6766_: usize,
    mut v_stop_6767_: usize,
) -> u8 {
    let mut v___x_6768_: u8 = 0;
    let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: u32 = 0;
    let mut v___x_6771_: u8 = 0;
    let mut v___x_6772_: usize = 0;
    let mut v___x_6773_: usize = 0;
    let mut v___x_6775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6768_ = lean_usize_dec_eq(v_i_6766_, v_stop_6767_);
                if v___x_6768_ == 0 {
                    v___x_6769_ = lean_array_uget_borrowed(v_as_6765_, v_i_6766_);
                    v___x_6770_ = leanh::lean_unbox_uint32(v___x_6769_);
                    v___x_6771_ = lean_uint32_dec_eq(v_a_6764_, v___x_6770_);
                    if v___x_6771_ == 0 {
                        v___x_6772_ = 1usize;
                        v___x_6773_ = lean_usize_add(v_i_6766_, v___x_6772_);
                        v_i_6766_ = v___x_6773_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6771_;
                    }
                } else {
                    v___x_6775_ = 0;
                    return v___x_6775_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0___boxed(
    mut v_a_6776_: *mut leanh::LeanObject,
    mut v_as_6777_: *mut leanh::LeanObject,
    mut v_i_6778_: *mut leanh::LeanObject,
    mut v_stop_6779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_6780_: u32 = 0;
    let mut v_i_boxed_6781_: usize = 0;
    let mut v_stop_boxed_6782_: usize = 0;
    let mut v_res_6783_: u8 = 0;
    let mut v_r_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_6780_ = leanh::lean_unbox_uint32(v_a_6776_);
    leanh::lean_dec(v_a_6776_);
    v_i_boxed_6781_ = leanh::lean_unbox_usize(v_i_6778_);
    leanh::lean_dec(v_i_6778_);
    v_stop_boxed_6782_ = leanh::lean_unbox_usize(v_stop_6779_);
    leanh::lean_dec(v_stop_6779_);
    v_res_6783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_boxed_6780_, v_as_6777_, v_i_boxed_6781_, v_stop_boxed_6782_);
    leanh::lean_dec_ref(v_as_6777_);
    v_r_6784_ = leanh::lean_box((v_res_6783_) as usize);
    return v_r_6784_;
}
pub unsafe fn l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(
    mut v_as_6785_: *mut leanh::LeanObject,
    mut v_a_6786_: u32,
) -> u8 {
    let mut v___x_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: u8 = 0;
    v___x_6787_ = leanh::lean_unsigned_to_nat(0);
    v___x_6788_ = lean_array_get_size(v_as_6785_);
    v___x_6789_ = lean_nat_dec_lt(v___x_6787_, v___x_6788_);
    if v___x_6789_ == 0 {
        return v___x_6789_;
    } else {
        if v___x_6789_ == 0 {
            return v___x_6789_;
        } else {
            let mut v___x_6790_: usize = 0;
            let mut v___x_6791_: usize = 0;
            let mut v___x_6792_: u8 = 0;
            v___x_6790_ = 0usize;
            v___x_6791_ = lean_usize_of_nat(v___x_6788_);
            v___x_6792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0_spec__0(v_a_6786_, v_as_6785_, v___x_6790_, v___x_6791_);
            return v___x_6792_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0___boxed(
    mut v_as_6793_: *mut leanh::LeanObject,
    mut v_a_6794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_6795_: u32 = 0;
    let mut v_res_6796_: u8 = 0;
    let mut v_r_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_6795_ = leanh::lean_unbox_uint32(v_a_6794_);
    leanh::lean_dec(v_a_6794_);
    v_res_6796_ =
        l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(v_as_6793_, v_a_boxed_6795_);
    leanh::lean_dec_ref(v_as_6793_);
    v_r_6797_ = leanh::lean_box((v_res_6796_) as usize);
    return v_r_6797_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_6803_: u32 = 0;
    let mut v___x_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6803_ = 42;
    v___x_6804_ = leanh::lean_box_uint32(v___x_6803_);
    return v___x_6804_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2()
-> *mut leanh::LeanObject {
    let mut v___x_6805_: u32 = 0;
    let mut v___x_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6805_ = 102;
    v___x_6806_ = leanh::lean_box_uint32(v___x_6805_);
    return v___x_6806_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3()
-> *mut leanh::LeanObject {
    let mut v___x_6807_: u32 = 0;
    let mut v___x_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6807_ = 101;
    v___x_6808_ = leanh::lean_box_uint32(v___x_6807_);
    return v___x_6808_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4()
-> *mut leanh::LeanObject {
    let mut v___x_6809_: u32 = 0;
    let mut v___x_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6809_ = 100;
    v___x_6810_ = leanh::lean_box_uint32(v___x_6809_);
    return v___x_6810_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5()
-> *mut leanh::LeanObject {
    let mut v___x_6811_: u32 = 0;
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6811_ = 99;
    v___x_6812_ = leanh::lean_box_uint32(v___x_6811_);
    return v___x_6812_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6()
-> *mut leanh::LeanObject {
    let mut v___x_6813_: u32 = 0;
    let mut v___x_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6813_ = 98;
    v___x_6814_ = leanh::lean_box_uint32(v___x_6813_);
    return v___x_6814_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7()
-> *mut leanh::LeanObject {
    let mut v___x_6815_: u32 = 0;
    let mut v___x_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6815_ = 97;
    v___x_6816_ = leanh::lean_box_uint32(v___x_6815_);
    return v___x_6816_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8()
-> *mut leanh::LeanObject {
    let mut v___x_6817_: u32 = 0;
    let mut v___x_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6817_ = 57;
    v___x_6818_ = leanh::lean_box_uint32(v___x_6817_);
    return v___x_6818_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9()
-> *mut leanh::LeanObject {
    let mut v___x_6819_: u32 = 0;
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6819_ = 56;
    v___x_6820_ = leanh::lean_box_uint32(v___x_6819_);
    return v___x_6820_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10()
-> *mut leanh::LeanObject {
    let mut v___x_6821_: u32 = 0;
    let mut v___x_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6821_ = 55;
    v___x_6822_ = leanh::lean_box_uint32(v___x_6821_);
    return v___x_6822_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11()
-> *mut leanh::LeanObject {
    let mut v___x_6823_: u32 = 0;
    let mut v___x_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6823_ = 54;
    v___x_6824_ = leanh::lean_box_uint32(v___x_6823_);
    return v___x_6824_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12()
-> *mut leanh::LeanObject {
    let mut v___x_6825_: u32 = 0;
    let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6825_ = 53;
    v___x_6826_ = leanh::lean_box_uint32(v___x_6825_);
    return v___x_6826_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13()
-> *mut leanh::LeanObject {
    let mut v___x_6827_: u32 = 0;
    let mut v___x_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6827_ = 52;
    v___x_6828_ = leanh::lean_box_uint32(v___x_6827_);
    return v___x_6828_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14()
-> *mut leanh::LeanObject {
    let mut v___x_6829_: u32 = 0;
    let mut v___x_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6829_ = 51;
    v___x_6830_ = leanh::lean_box_uint32(v___x_6829_);
    return v___x_6830_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15()
-> *mut leanh::LeanObject {
    let mut v___x_6831_: u32 = 0;
    let mut v___x_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6831_ = 50;
    v___x_6832_ = leanh::lean_box_uint32(v___x_6831_);
    return v___x_6832_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16()
-> *mut leanh::LeanObject {
    let mut v___x_6833_: u32 = 0;
    let mut v___x_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6833_ = 49;
    v___x_6834_ = leanh::lean_box_uint32(v___x_6833_);
    return v___x_6834_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17()
-> *mut leanh::LeanObject {
    let mut v___x_6835_: u32 = 0;
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6835_ = 48;
    v___x_6836_ = leanh::lean_box_uint32(v___x_6835_);
    return v___x_6836_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6837_ = leanh::lean_unsigned_to_nat(17);
    v___x_6838_ = lean_mk_empty_array_with_capacity(v___x_6837_);
    v___x_6839_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17;
    v___x_6840_ = lean_array_push(v___x_6838_, v___x_6839_);
    v___x_6841_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16;
    v___x_6842_ = lean_array_push(v___x_6840_, v___x_6841_);
    v___x_6843_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15;
    v___x_6844_ = lean_array_push(v___x_6842_, v___x_6843_);
    v___x_6845_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14;
    v___x_6846_ = lean_array_push(v___x_6844_, v___x_6845_);
    v___x_6847_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13;
    v___x_6848_ = lean_array_push(v___x_6846_, v___x_6847_);
    v___x_6849_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12;
    v___x_6850_ = lean_array_push(v___x_6848_, v___x_6849_);
    v___x_6851_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11;
    v___x_6852_ = lean_array_push(v___x_6850_, v___x_6851_);
    v___x_6853_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10;
    v___x_6854_ = lean_array_push(v___x_6852_, v___x_6853_);
    v___x_6855_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9;
    v___x_6856_ = lean_array_push(v___x_6854_, v___x_6855_);
    v___x_6857_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8;
    v___x_6858_ = lean_array_push(v___x_6856_, v___x_6857_);
    v___x_6859_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7;
    v___x_6860_ = lean_array_push(v___x_6858_, v___x_6859_);
    v___x_6861_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6;
    v___x_6862_ = lean_array_push(v___x_6860_, v___x_6861_);
    v___x_6863_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5;
    v___x_6864_ = lean_array_push(v___x_6862_, v___x_6863_);
    v___x_6865_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4;
    v___x_6866_ = lean_array_push(v___x_6864_, v___x_6865_);
    v___x_6867_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3;
    v___x_6868_ = lean_array_push(v___x_6866_, v___x_6867_);
    v___x_6869_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2;
    v___x_6870_ = lean_array_push(v___x_6868_, v___x_6869_);
    v___x_6871_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1;
    v___x_6872_ = lean_array_push(v___x_6870_, v___x_6871_);
    return v___x_6872_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6877_ = leanh::lean_box(0);
    v___x_6878_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__5;
    v___x_6879_ = l_Lean_mkConst(v___x_6878_, v___x_6877_);
    return v___x_6879_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_6883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6883_ = leanh::lean_box(0);
    v___x_6884_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__8;
    v___x_6885_ = l_Lean_mkConst(v___x_6884_, v___x_6883_);
    return v___x_6885_;
}
pub unsafe fn _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6889_ = leanh::lean_box(0);
    v___x_6890_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__11;
    v___x_6891_ = l_Lean_mkConst(v___x_6890_, v___x_6889_);
    return v___x_6891_;
}
pub unsafe fn l_Char_Nat_reduceDigitCharEq___redArg(
    mut v_e_6892_: *mut leanh::LeanObject,
    mut v_a_6893_: *mut leanh::LeanObject,
    mut v_a_6894_: *mut leanh::LeanObject,
    mut v_a_6895_: *mut leanh::LeanObject,
    mut v_a_6896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: u8 = 0;
    let mut v___x_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: u8 = 0;
    let mut v___x_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6915_: u8 = 0;
    let mut v_val_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6919_: u8 = 0;
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: u32 = 0;
    let mut v___x_6922_: u8 = 0;
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6942_: u8 = 0;
    let mut v___x_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6947_: u8 = 0;
    let mut v_a_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6951_: u8 = 0;
    let mut v___x_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6955_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6898_ = l_Char_reduceEq___redArg___closed__1;
                v___x_6899_ = leanh::lean_unsigned_to_nat(3);
                v___x_6900_ = l_Lean_Expr_isAppOfArity(v_e_6892_, v___x_6898_, v___x_6899_);
                if v___x_6900_ == 0 {
                    leanh::lean_dec_ref(v_e_6892_);
                    v___x_6901_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_6902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6902_, 0, v___x_6901_);
                    return v___x_6902_;
                } else {
                    v___x_6903_ = l_Lean_Expr_appFn_x21(v_e_6892_);
                    v_lhs_6904_ = l_Lean_Expr_appArg_x21(v___x_6903_);
                    leanh::lean_dec_ref(v___x_6903_);
                    v___x_6905_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__2;
                    v___x_6906_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6907_ = l_Lean_Expr_isAppOfArity(v_lhs_6904_, v___x_6905_, v___x_6906_);
                    if v___x_6907_ == 0 {
                        leanh::lean_dec_ref(v_lhs_6904_);
                        leanh::lean_dec_ref(v_e_6892_);
                        v___x_6908_ = l_Char_reduceBinPred___redArg___closed__0;
                        v___x_6909_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6909_, 0, v___x_6908_);
                        return v___x_6909_;
                    } else {
                        v_rhs_6910_ = l_Lean_Expr_appArg_x21(v_e_6892_);
                        leanh::lean_inc_ref(v_rhs_6910_);
                        v___x_6911_ = l_Lean_Meta_getCharValue_x3f(
                            v_rhs_6910_,
                            v_a_6893_,
                            v_a_6894_,
                            v_a_6895_,
                            v_a_6896_,
                        );
                        if leanh::lean_obj_tag(v___x_6911_) == 0 {
                            v_a_6912_ = leanh::lean_ctor_get(v___x_6911_, 0);
                            v_isSharedCheck_6947_ =
                                (!leanh::lean_is_exclusive(v___x_6911_)) as u8;
                            if v_isSharedCheck_6947_ == 0 {
                                v___x_6914_ = v___x_6911_;
                                v_isShared_6915_ = v_isSharedCheck_6947_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6912_);
                                leanh::lean_dec(v___x_6911_);
                                v___x_6914_ = leanh::lean_box(0);
                                v_isShared_6915_ = v_isSharedCheck_6947_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_rhs_6910_);
                            leanh::lean_dec_ref(v_lhs_6904_);
                            leanh::lean_dec_ref(v_e_6892_);
                            v_a_6948_ = leanh::lean_ctor_get(v___x_6911_, 0);
                            v_isSharedCheck_6955_ =
                                (!leanh::lean_is_exclusive(v___x_6911_)) as u8;
                            if v_isSharedCheck_6955_ == 0 {
                                v___x_6950_ = v___x_6911_;
                                v_isShared_6951_ = v_isSharedCheck_6955_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6948_);
                                leanh::lean_dec(v___x_6911_);
                                v___x_6950_ = leanh::lean_box(0);
                                v_isShared_6951_ = v_isSharedCheck_6955_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6912_) == 1 {
                    v_val_6916_ = leanh::lean_ctor_get(v_a_6912_, 0);
                    v_isSharedCheck_6942_ = (!leanh::lean_is_exclusive(v_a_6912_)) as u8;
                    if v_isSharedCheck_6942_ == 0 {
                        v___x_6918_ = v_a_6912_;
                        v_isShared_6919_ = v_isSharedCheck_6942_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6916_);
                        leanh::lean_dec(v_a_6912_);
                        v___x_6918_ = leanh::lean_box(0);
                        v_isShared_6919_ = v_isSharedCheck_6942_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6912_);
                    leanh::lean_dec_ref(v_rhs_6910_);
                    leanh::lean_dec_ref(v_lhs_6904_);
                    leanh::lean_dec_ref(v_e_6892_);
                    v___x_6943_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_6915_ == 0 {
                        leanh::lean_ctor_set(v___x_6914_, 0, v___x_6943_);
                        v___x_6945_ = v___x_6914_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6946_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6946_, 0, v___x_6943_);
                        v___x_6945_ = v_reuseFailAlloc_6946_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6920_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once),
                    _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3,
                );
                v___x_6921_ = leanh::lean_unbox_uint32(v_val_6916_);
                leanh::lean_dec(v_val_6916_);
                v___x_6922_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(
                    v___x_6920_,
                    v___x_6921_,
                );
                if v___x_6922_ == 0 {
                    v___x_6923_ = l_Lean_Expr_appArg_x21(v_lhs_6904_);
                    leanh::lean_dec_ref(v_lhs_6904_);
                    v___x_6924_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once
                        ),
                        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6,
                    );
                    v___x_6925_ = l_Lean_eagerReflBoolTrue;
                    v___x_6926_ = l_Lean_mkApp3(v___x_6924_, v___x_6923_, v_rhs_6910_, v___x_6925_);
                    v___x_6927_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once
                        ),
                        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9,
                    );
                    v___x_6928_ = l_Lean_mkAppB(v___x_6927_, v_e_6892_, v___x_6926_);
                    v___x_6929_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__12),
                        core::ptr::addr_of_mut!(
                            l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once
                        ),
                        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12,
                    );
                    if v_isShared_6919_ == 0 {
                        leanh::lean_ctor_set(v___x_6918_, 0, v___x_6928_);
                        v___x_6931_ = v___x_6918_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6937_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6937_, 0, v___x_6928_);
                        v___x_6931_ = v_reuseFailAlloc_6937_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6918_);
                    leanh::lean_dec_ref(v_rhs_6910_);
                    leanh::lean_dec_ref(v_lhs_6904_);
                    leanh::lean_dec_ref(v_e_6892_);
                    v___x_6938_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_6915_ == 0 {
                        leanh::lean_ctor_set(v___x_6914_, 0, v___x_6938_);
                        v___x_6940_ = v___x_6914_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6941_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6941_, 0, v___x_6938_);
                        v___x_6940_ = v_reuseFailAlloc_6941_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6932_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_6932_, 0, v___x_6929_);
                leanh::lean_ctor_set(v___x_6932_, 1, v___x_6931_);
                leanh::lean_ctor_set_uint8(
                    v___x_6932_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_6907_,
                );
                v___x_6933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6933_, 0, v___x_6932_);
                if v_isShared_6915_ == 0 {
                    leanh::lean_ctor_set(v___x_6914_, 0, v___x_6933_);
                    v___x_6935_ = v___x_6914_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6936_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6936_, 0, v___x_6933_);
                    v___x_6935_ = v_reuseFailAlloc_6936_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6935_;
            }
            5 => {
                return v___x_6940_;
            }
            6 => {
                return v___x_6945_;
            }
            7 => {
                if v_isShared_6951_ == 0 {
                    v___x_6953_ = v___x_6950_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6954_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6954_, 0, v_a_6948_);
                    v___x_6953_ = v_reuseFailAlloc_6954_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_Nat_reduceDigitCharEq___redArg___boxed(
    mut v_e_6956_: *mut leanh::LeanObject,
    mut v_a_6957_: *mut leanh::LeanObject,
    mut v_a_6958_: *mut leanh::LeanObject,
    mut v_a_6959_: *mut leanh::LeanObject,
    mut v_a_6960_: *mut leanh::LeanObject,
    mut v_a_6961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6962_ = l_Char_Nat_reduceDigitCharEq___redArg(
        v_e_6956_, v_a_6957_, v_a_6958_, v_a_6959_, v_a_6960_,
    );
    leanh::lean_dec(v_a_6960_);
    leanh::lean_dec_ref(v_a_6959_);
    leanh::lean_dec(v_a_6958_);
    leanh::lean_dec_ref(v_a_6957_);
    return v_res_6962_;
}
pub unsafe fn l_Char_Nat_reduceDigitCharEq(
    mut v_e_6963_: *mut leanh::LeanObject,
    mut v_a_6964_: *mut leanh::LeanObject,
    mut v_a_6965_: *mut leanh::LeanObject,
    mut v_a_6966_: *mut leanh::LeanObject,
    mut v_a_6967_: *mut leanh::LeanObject,
    mut v_a_6968_: *mut leanh::LeanObject,
    mut v_a_6969_: *mut leanh::LeanObject,
    mut v_a_6970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6972_ = l_Char_Nat_reduceDigitCharEq___redArg(
        v_e_6963_, v_a_6967_, v_a_6968_, v_a_6969_, v_a_6970_,
    );
    return v___x_6972_;
}
pub unsafe fn l_Char_Nat_reduceDigitCharEq___boxed(
    mut v_e_6973_: *mut leanh::LeanObject,
    mut v_a_6974_: *mut leanh::LeanObject,
    mut v_a_6975_: *mut leanh::LeanObject,
    mut v_a_6976_: *mut leanh::LeanObject,
    mut v_a_6977_: *mut leanh::LeanObject,
    mut v_a_6978_: *mut leanh::LeanObject,
    mut v_a_6979_: *mut leanh::LeanObject,
    mut v_a_6980_: *mut leanh::LeanObject,
    mut v_a_6981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6982_ = l_Char_Nat_reduceDigitCharEq(
        v_e_6973_, v_a_6974_, v_a_6975_, v_a_6976_, v_a_6977_, v_a_6978_, v_a_6979_, v_a_6980_,
    );
    leanh::lean_dec(v_a_6980_);
    leanh::lean_dec_ref(v_a_6979_);
    leanh::lean_dec(v_a_6978_);
    leanh::lean_dec_ref(v_a_6977_);
    leanh::lean_dec(v_a_6976_);
    leanh::lean_dec_ref(v_a_6975_);
    leanh::lean_dec(v_a_6974_);
    return v_res_6982_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_()
-> *mut leanh::LeanObject {
    let mut v___x_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7003_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_;
    v___x_7004_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_;
    v___x_7005_ = leanh::lean_alloc_closure(
        l_Char_Nat_reduceDigitCharEq___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_7006_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_7003_, v___x_7004_, v___x_7005_);
    return v___x_7006_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23____boxed(
    mut v_a_7007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7008_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_();
    return v_res_7008_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_()
-> *mut leanh::LeanObject {
    let mut v___x_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7009_ = leanh::lean_alloc_closure(
        l_Char_Nat_reduceDigitCharEq___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_7010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7010_, 0, v___x_7009_);
    return v___x_7010_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_()
-> *mut leanh::LeanObject {
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: u8 = 0;
    let mut v___x_7014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7012_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_;
    v___x_7013_ = 1;
    v___x_7014_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_);
    v___x_7015_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_7012_, v___x_7013_, v___x_7014_);
    return v___x_7015_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25____boxed(
    mut v_a_7016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7017_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_();
    return v_res_7017_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27_()
-> *mut leanh::LeanObject {
    let mut v___x_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: u8 = 0;
    let mut v___x_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7019_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_;
    v___x_7020_ = 1;
    v___x_7021_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_);
    v___x_7022_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_7019_, v___x_7020_, v___x_7021_);
    return v___x_7022_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27____boxed(
    mut v_a_7023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7024_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27_();
    return v_res_7024_;
}
pub unsafe fn _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7029_ = leanh::lean_box(0);
    v___x_7030_ = l_Lean_Level_succ___override(v___x_7029_);
    return v___x_7030_;
}
pub unsafe fn _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7031_ = leanh::lean_box(0);
    v___x_7032_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_Nat_reduceEqDigitChar___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Char_Nat_reduceEqDigitChar___redArg___closed__2_once),
        _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__2,
    );
    v___x_7033_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7033_, 0, v___x_7032_);
    leanh::lean_ctor_set(v___x_7033_, 1, v___x_7031_);
    return v___x_7033_;
}
pub unsafe fn _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_7034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7034_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Char_Nat_reduceEqDigitChar___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Char_Nat_reduceEqDigitChar___redArg___closed__3_once),
        _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__3,
    );
    v___x_7035_ = l_Char_Nat_reduceEqDigitChar___redArg___closed__1;
    v___x_7036_ = l_Lean_mkConst(v___x_7035_, v___x_7034_);
    return v___x_7036_;
}
pub unsafe fn _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_7037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7037_ = leanh::lean_box(0);
    v___x_7038_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_;
    v___x_7039_ = l_Lean_mkConst(v___x_7038_, v___x_7037_);
    return v___x_7039_;
}
pub unsafe fn l_Char_Nat_reduceEqDigitChar___redArg(
    mut v_e_7040_: *mut leanh::LeanObject,
    mut v_a_7041_: *mut leanh::LeanObject,
    mut v_a_7042_: *mut leanh::LeanObject,
    mut v_a_7043_: *mut leanh::LeanObject,
    mut v_a_7044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: u8 = 0;
    let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_digitCharExpr_7051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: u8 = 0;
    let mut v___x_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charExpr_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7063_: u8 = 0;
    let mut v_val_7064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7067_: u8 = 0;
    let mut v___x_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: u32 = 0;
    let mut v___x_7070_: u8 = 0;
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7093_: u8 = 0;
    let mut v___x_7094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7098_: u8 = 0;
    let mut v_a_7099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7102_: u8 = 0;
    let mut v___x_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7046_ = l_Char_reduceEq___redArg___closed__1;
                v___x_7047_ = leanh::lean_unsigned_to_nat(3);
                v___x_7048_ = l_Lean_Expr_isAppOfArity(v_e_7040_, v___x_7046_, v___x_7047_);
                if v___x_7048_ == 0 {
                    leanh::lean_dec_ref(v_e_7040_);
                    v___x_7049_ = l_Char_reduceBinPred___redArg___closed__0;
                    v___x_7050_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7050_, 0, v___x_7049_);
                    return v___x_7050_;
                } else {
                    v_digitCharExpr_7051_ = l_Lean_Expr_appArg_x21(v_e_7040_);
                    v___x_7052_ = l_Char_Nat_reduceDigitCharEq___redArg___closed__2;
                    v___x_7053_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7054_ =
                        l_Lean_Expr_isAppOfArity(v_digitCharExpr_7051_, v___x_7052_, v___x_7053_);
                    if v___x_7054_ == 0 {
                        leanh::lean_dec_ref(v_digitCharExpr_7051_);
                        leanh::lean_dec_ref(v_e_7040_);
                        v___x_7055_ = l_Char_reduceBinPred___redArg___closed__0;
                        v___x_7056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7056_, 0, v___x_7055_);
                        return v___x_7056_;
                    } else {
                        v___x_7057_ = l_Lean_Expr_appFn_x21(v_e_7040_);
                        v_charExpr_7058_ = l_Lean_Expr_appArg_x21(v___x_7057_);
                        leanh::lean_dec_ref(v___x_7057_);
                        leanh::lean_inc_ref(v_charExpr_7058_);
                        v___x_7059_ = l_Lean_Meta_getCharValue_x3f(
                            v_charExpr_7058_,
                            v_a_7041_,
                            v_a_7042_,
                            v_a_7043_,
                            v_a_7044_,
                        );
                        if leanh::lean_obj_tag(v___x_7059_) == 0 {
                            v_a_7060_ = leanh::lean_ctor_get(v___x_7059_, 0);
                            v_isSharedCheck_7098_ =
                                (!leanh::lean_is_exclusive(v___x_7059_)) as u8;
                            if v_isSharedCheck_7098_ == 0 {
                                v___x_7062_ = v___x_7059_;
                                v_isShared_7063_ = v_isSharedCheck_7098_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7060_);
                                leanh::lean_dec(v___x_7059_);
                                v___x_7062_ = leanh::lean_box(0);
                                v_isShared_7063_ = v_isSharedCheck_7098_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_charExpr_7058_);
                            leanh::lean_dec_ref(v_digitCharExpr_7051_);
                            leanh::lean_dec_ref(v_e_7040_);
                            v_a_7099_ = leanh::lean_ctor_get(v___x_7059_, 0);
                            v_isSharedCheck_7106_ =
                                (!leanh::lean_is_exclusive(v___x_7059_)) as u8;
                            if v_isSharedCheck_7106_ == 0 {
                                v___x_7101_ = v___x_7059_;
                                v_isShared_7102_ = v_isSharedCheck_7106_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7099_);
                                leanh::lean_dec(v___x_7059_);
                                v___x_7101_ = leanh::lean_box(0);
                                v_isShared_7102_ = v_isSharedCheck_7106_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_7060_) == 1 {
                    v_val_7064_ = leanh::lean_ctor_get(v_a_7060_, 0);
                    v_isSharedCheck_7093_ = (!leanh::lean_is_exclusive(v_a_7060_)) as u8;
                    if v_isSharedCheck_7093_ == 0 {
                        v___x_7066_ = v_a_7060_;
                        v_isShared_7067_ = v_isSharedCheck_7093_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7064_);
                        leanh::lean_dec(v_a_7060_);
                        v___x_7066_ = leanh::lean_box(0);
                        v_isShared_7067_ = v_isSharedCheck_7093_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7060_);
                    leanh::lean_dec_ref(v_charExpr_7058_);
                    leanh::lean_dec_ref(v_digitCharExpr_7051_);
                    leanh::lean_dec_ref(v_e_7040_);
                    v___x_7094_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_7063_ == 0 {
                        leanh::lean_ctor_set(v___x_7062_, 0, v___x_7094_);
                        v___x_7096_ = v___x_7062_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7097_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7097_, 0, v___x_7094_);
                        v___x_7096_ = v_reuseFailAlloc_7097_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7068_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__3_once),
                    _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3,
                );
                v___x_7069_ = leanh::lean_unbox_uint32(v_val_7064_);
                leanh::lean_dec(v_val_7064_);
                v___x_7070_ = l_Array_contains___at___00Char_Nat_reduceDigitCharEq_spec__0(
                    v___x_7068_,
                    v___x_7069_,
                );
                if v___x_7070_ == 0 {
                    v___x_7071_ = l_Lean_Expr_appArg_x21(v_digitCharExpr_7051_);
                    v___x_7072_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Char_Nat_reduceDigitCharEq___redArg___closed__6_once
                        ),
                        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__6,
                    );
                    v___x_7073_ = l_Lean_eagerReflBoolTrue;
                    leanh::lean_inc_ref(v_charExpr_7058_);
                    v___x_7074_ =
                        l_Lean_mkApp3(v___x_7072_, v___x_7071_, v_charExpr_7058_, v___x_7073_);
                    v___x_7075_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_Nat_reduceEqDigitChar___redArg___closed__4),
                        core::ptr::addr_of_mut!(
                            l_Char_Nat_reduceEqDigitChar___redArg___closed__4_once
                        ),
                        _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__4,
                    );
                    v___x_7076_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_Nat_reduceEqDigitChar___redArg___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Char_Nat_reduceEqDigitChar___redArg___closed__5_once
                        ),
                        _init_l_Char_Nat_reduceEqDigitChar___redArg___closed__5,
                    );
                    v___x_7077_ = l_Lean_mkApp4(
                        v___x_7075_,
                        v___x_7076_,
                        v_digitCharExpr_7051_,
                        v_charExpr_7058_,
                        v___x_7074_,
                    );
                    v___x_7078_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Char_Nat_reduceDigitCharEq___redArg___closed__9_once
                        ),
                        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__9,
                    );
                    v___x_7079_ = l_Lean_mkAppB(v___x_7078_, v_e_7040_, v___x_7077_);
                    v___x_7080_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Char_Nat_reduceDigitCharEq___redArg___closed__12),
                        core::ptr::addr_of_mut!(
                            l_Char_Nat_reduceDigitCharEq___redArg___closed__12_once
                        ),
                        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__12,
                    );
                    if v_isShared_7067_ == 0 {
                        leanh::lean_ctor_set(v___x_7066_, 0, v___x_7079_);
                        v___x_7082_ = v___x_7066_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7088_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 0, v___x_7079_);
                        v___x_7082_ = v_reuseFailAlloc_7088_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7066_);
                    leanh::lean_dec_ref(v_charExpr_7058_);
                    leanh::lean_dec_ref(v_digitCharExpr_7051_);
                    leanh::lean_dec_ref(v_e_7040_);
                    v___x_7089_ = l_Char_reduceBinPred___redArg___closed__0;
                    if v_isShared_7063_ == 0 {
                        leanh::lean_ctor_set(v___x_7062_, 0, v___x_7089_);
                        v___x_7091_ = v___x_7062_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7092_, 0, v___x_7089_);
                        v___x_7091_ = v_reuseFailAlloc_7092_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7083_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_7083_, 0, v___x_7080_);
                leanh::lean_ctor_set(v___x_7083_, 1, v___x_7082_);
                leanh::lean_ctor_set_uint8(
                    v___x_7083_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_7054_,
                );
                v___x_7084_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7084_, 0, v___x_7083_);
                if v_isShared_7063_ == 0 {
                    leanh::lean_ctor_set(v___x_7062_, 0, v___x_7084_);
                    v___x_7086_ = v___x_7062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7087_, 0, v___x_7084_);
                    v___x_7086_ = v_reuseFailAlloc_7087_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7086_;
            }
            5 => {
                return v___x_7091_;
            }
            6 => {
                return v___x_7096_;
            }
            7 => {
                if v_isShared_7102_ == 0 {
                    v___x_7104_ = v___x_7101_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7105_, 0, v_a_7099_);
                    v___x_7104_ = v_reuseFailAlloc_7105_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_Nat_reduceEqDigitChar___redArg___boxed(
    mut v_e_7107_: *mut leanh::LeanObject,
    mut v_a_7108_: *mut leanh::LeanObject,
    mut v_a_7109_: *mut leanh::LeanObject,
    mut v_a_7110_: *mut leanh::LeanObject,
    mut v_a_7111_: *mut leanh::LeanObject,
    mut v_a_7112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7113_ = l_Char_Nat_reduceEqDigitChar___redArg(
        v_e_7107_, v_a_7108_, v_a_7109_, v_a_7110_, v_a_7111_,
    );
    leanh::lean_dec(v_a_7111_);
    leanh::lean_dec_ref(v_a_7110_);
    leanh::lean_dec(v_a_7109_);
    leanh::lean_dec_ref(v_a_7108_);
    return v_res_7113_;
}
pub unsafe fn l_Char_Nat_reduceEqDigitChar(
    mut v_e_7114_: *mut leanh::LeanObject,
    mut v_a_7115_: *mut leanh::LeanObject,
    mut v_a_7116_: *mut leanh::LeanObject,
    mut v_a_7117_: *mut leanh::LeanObject,
    mut v_a_7118_: *mut leanh::LeanObject,
    mut v_a_7119_: *mut leanh::LeanObject,
    mut v_a_7120_: *mut leanh::LeanObject,
    mut v_a_7121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7123_ = l_Char_Nat_reduceEqDigitChar___redArg(
        v_e_7114_, v_a_7118_, v_a_7119_, v_a_7120_, v_a_7121_,
    );
    return v___x_7123_;
}
pub unsafe fn l_Char_Nat_reduceEqDigitChar___boxed(
    mut v_e_7124_: *mut leanh::LeanObject,
    mut v_a_7125_: *mut leanh::LeanObject,
    mut v_a_7126_: *mut leanh::LeanObject,
    mut v_a_7127_: *mut leanh::LeanObject,
    mut v_a_7128_: *mut leanh::LeanObject,
    mut v_a_7129_: *mut leanh::LeanObject,
    mut v_a_7130_: *mut leanh::LeanObject,
    mut v_a_7131_: *mut leanh::LeanObject,
    mut v_a_7132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7133_ = l_Char_Nat_reduceEqDigitChar(
        v_e_7124_, v_a_7125_, v_a_7126_, v_a_7127_, v_a_7128_, v_a_7129_, v_a_7130_, v_a_7131_,
    );
    leanh::lean_dec(v_a_7131_);
    leanh::lean_dec_ref(v_a_7130_);
    leanh::lean_dec(v_a_7129_);
    leanh::lean_dec_ref(v_a_7128_);
    leanh::lean_dec(v_a_7127_);
    leanh::lean_dec_ref(v_a_7126_);
    leanh::lean_dec(v_a_7125_);
    return v_res_7133_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_()
-> *mut leanh::LeanObject {
    let mut v___x_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7151_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_;
    v___x_7152_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_;
    v___x_7153_ = leanh::lean_alloc_closure(
        l_Char_Nat_reduceEqDigitChar___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_7154_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_7151_, v___x_7152_, v___x_7153_);
    return v___x_7154_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23____boxed(
    mut v_a_7155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7156_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_();
    return v_res_7156_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_()
-> *mut leanh::LeanObject {
    let mut v___x_7157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7157_ = leanh::lean_alloc_closure(
        l_Char_Nat_reduceEqDigitChar___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_7158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7158_, 0, v___x_7157_);
    return v___x_7158_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_()
-> *mut leanh::LeanObject {
    let mut v___x_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: u8 = 0;
    let mut v___x_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7160_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_;
    v___x_7161_ = 1;
    v___x_7162_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_);
    v___x_7163_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_7160_, v___x_7161_, v___x_7162_);
    return v___x_7163_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25____boxed(
    mut v_a_7164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7165_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_();
    return v_res_7165_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27_()
-> *mut leanh::LeanObject {
    let mut v___x_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: u8 = 0;
    let mut v___x_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_;
    v___x_7168_ = 1;
    v___x_7169_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_);
    v___x_7170_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_7167_, v___x_7168_, v___x_7169_);
    return v___x_7170_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27____boxed(
    mut v_a_7171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7172_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27_();
    return v_res_7172_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToLower_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToLower___regBuiltin_Char_reduceToLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_334306140____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToUpper_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToUpper___regBuiltin_Char_reduceToUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_867852127____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToNat_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToNat___regBuiltin_Char_reduceToNat_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3228376024____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsWhitespace_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsWhitespace___regBuiltin_Char_reduceIsWhitespace_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2159514887____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsUpper_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsUpper___regBuiltin_Char_reduceIsUpper_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2972409855____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsLower_declare__43_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsLower___regBuiltin_Char_reduceIsLower_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3550415474____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlpha_declare__48_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlpha___regBuiltin_Char_reduceIsAlpha_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1470229681____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsDigit_declare__53_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsDigit___regBuiltin_Char_reduceIsDigit_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2080780882____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceIsAlphaNum_declare__58_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceIsAlphaNum___regBuiltin_Char_reduceIsAlphaNum_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1090167397____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceToString_declare__63_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_16_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_18_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceToString___regBuiltin_Char_reduceToString_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2368443037____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceVal_declare__68_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceVal___regBuiltin_Char_reduceVal_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2778720590____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLT_declare__73_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLT___regBuiltin_Char_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1414161310____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceLE_declare__78_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceLE___regBuiltin_Char_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_702568235____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGT_declare__83_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGT___regBuiltin_Char_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1826190098____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceGE_declare__88_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceGE___regBuiltin_Char_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_623401654____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceEq_declare__93_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceEq___regBuiltin_Char_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_936367716____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceNe_declare__98_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceNe___regBuiltin_Char_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2880200834____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBEq_declare__103_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBEq___regBuiltin_Char_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2122723960____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceBNe_declare__108_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_20_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_22_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceBNe___regBuiltin_Char_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2284039980____hygCtx___hyg_24_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_isValue_declare__113_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_isValue___regBuiltin_Char_isValue_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_2709388253____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceOfNatAux_declare__118_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_14_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_16_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceOfNatAux___regBuiltin_Char_reduceOfNatAux_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1314572429____hygCtx___hyg_18_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_reduceDefault_declare__123_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_reduceDefault___regBuiltin_Char_reduceDefault_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_1879646975____hygCtx___hyg_19_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__1,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__2,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__3,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__4,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__5,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__6,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__7,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__8,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__9,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__10,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__11,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__12,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__13,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__14,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__15,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__16,
    );
    l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17 =
        _init_l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17();
    leanh::lean_mark_persistent(
        l_Char_Nat_reduceDigitCharEq___redArg___closed__3___boxed__const__17,
    );
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceDigitCharEq_declare__128_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_23_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_25_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceDigitCharEq___regBuiltin_Char_Nat_reduceDigitCharEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_3666384508____hygCtx___hyg_27_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0____regBuiltin_Char_Nat_reduceEqDigitChar_declare__133_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_23_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_25_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_0__Char_Nat_reduceEqDigitChar___regBuiltin_Char_Nat_reduceEqDigitChar_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char_4145659166____hygCtx___hyg_27_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
}