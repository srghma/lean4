// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
// Imports: Init.Simproc Lean.Meta.Tactic.Simp.Simproc Lean.Meta.CtorRecognizer
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
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
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Simp::Types::lean_simp;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_uint64,
    lean_unsigned_to_nat,
};
pub static l_reduceIte___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_reduceIte___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__0_value) as *mut LeanObject;
pub static l_reduceIte___closed__1_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceIte___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__1_value) as *mut LeanObject;
pub static l_reduceIte___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceIte___closed__1_value) as *mut LeanObject,
        18356704233129443855 as *mut LeanObject,
    ],
};
static mut l_reduceIte___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__2_value) as *mut LeanObject;
pub static l_reduceIte___closed__3_value: LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceIte___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__3_value) as *mut LeanObject;
pub static l_reduceIte___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceIte___closed__3_value) as *mut LeanObject,
        15684782314253460228 as *mut LeanObject,
    ],
};
static mut l_reduceIte___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__4_value) as *mut LeanObject;
pub static l_reduceIte___closed__5_value: LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceIte___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__5_value) as *mut LeanObject;
pub static l_reduceIte___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceIte___closed__5_value) as *mut LeanObject,
        7490975742882862809 as *mut LeanObject,
    ],
};
static mut l_reduceIte___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_reduceIte___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut LeanObject,13377587881735534081 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_reduceIte___closed__2_value) as *mut LeanObject,((( 5 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value: LeanArrayObject<6> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_: *mut LeanObject = core::ptr::null_mut();
pub static l_reduceDIte___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceDIte___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__0_value) as *mut LeanObject;
pub static l_reduceDIte___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceDIte___closed__0_value) as *mut LeanObject,
        8391571994004792969 as *mut LeanObject,
    ],
};
static mut l_reduceDIte___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__1_value) as *mut LeanObject;
pub static l_reduceDIte___closed__2_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceDIte___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__2_value) as *mut LeanObject;
pub static l_reduceDIte___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceDIte___closed__2_value) as *mut LeanObject,
        712644580193758902 as *mut LeanObject,
    ],
};
static mut l_reduceDIte___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__3_value) as *mut LeanObject;
static mut l_reduceDIte___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_reduceDIte___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_reduceDIte___closed__5_value: LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceDIte___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__5_value) as *mut LeanObject;
pub static l_reduceDIte___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceDIte___closed__5_value) as *mut LeanObject,
        15303888708270464921 as *mut LeanObject,
    ],
};
static mut l_reduceDIte___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__6_value) as *mut LeanObject;
pub static l_reduceDIte___closed__7_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceDIte___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__7_value) as *mut LeanObject;
pub static l_reduceDIte___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceDIte___closed__7_value) as *mut LeanObject,
        12884550255617431732 as *mut LeanObject,
    ],
};
static mut l_reduceDIte___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__8_value) as *mut LeanObject;
static mut l_reduceDIte___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_reduceDIte___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_reduceDIte___closed__10_value: LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceDIte___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__10_value) as *mut LeanObject;
pub static l_reduceDIte___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceDIte___closed__10_value) as *mut LeanObject,
        187051596005140493 as *mut LeanObject,
    ],
};
static mut l_reduceDIte___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_reduceDIte___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 100, 117, 99, 101, 68, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut LeanObject,5427593982451803422 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_reduceDIte___closed__1_value) as *mut LeanObject,((( 5 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value: LeanArrayObject<6> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_: *mut LeanObject = core::ptr::null_mut();
pub static l_dreduceIte___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_dreduceIte___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__0_value) as *mut LeanObject;
pub static l_dreduceIte___closed__1_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_dreduceIte___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__1_value) as *mut LeanObject;
pub static l_dreduceIte___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_dreduceIte___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__2_value) as *mut LeanObject;
static l_dreduceIte___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_dreduceIte___closed__1_value) as *mut LeanObject,
        4342836574150310743 as *mut LeanObject,
    ],
};
pub static l_dreduceIte___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_dreduceIte___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_dreduceIte___closed__2_value) as *mut LeanObject,
        14734865452941588245 as *mut LeanObject,
    ],
};
static mut l_dreduceIte___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__3_value) as *mut LeanObject;
pub static l_dreduceIte___closed__4_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_dreduceIte___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__4_value) as *mut LeanObject;
static l_dreduceIte___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_dreduceIte___closed__1_value) as *mut LeanObject,
        4342836574150310743 as *mut LeanObject,
    ],
};
pub static l_dreduceIte___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_dreduceIte___closed__5_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_dreduceIte___closed__4_value) as *mut LeanObject,
        83052734847462153 as *mut LeanObject,
    ],
};
static mut l_dreduceIte___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_dreduceIte___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 114, 101, 100, 117, 99, 101, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value) as *mut LeanObject,18396871770522245140 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 114, 101, 100, 117, 99, 101, 68, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value) as *mut LeanObject,3968518033955806430 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_: *mut LeanObject = core::ptr::null_mut();
pub static l_reduceCtorEq___lam__2___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceCtorEq___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___lam__2___closed__0_value) as *mut LeanObject;
pub static l_reduceCtorEq___lam__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceCtorEq___lam__2___closed__0_value) as *mut LeanObject,
        907667957179513571 as *mut LeanObject,
    ],
};
static mut l_reduceCtorEq___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___lam__2___closed__1_value) as *mut LeanObject;
static mut l_reduceCtorEq___lam__2___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_reduceCtorEq___lam__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_reduceCtorEq___lam__2___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_reduceCtorEq___lam__2___closed__3: u64 = 0;
static mut l_reduceCtorEq___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_reduceCtorEq___closed__0: u64 = 0;
pub static l_reduceCtorEq___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceCtorEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___closed__1_value) as *mut LeanObject;
pub static l_reduceCtorEq___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceCtorEq___closed__1_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_reduceCtorEq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___closed__2_value) as *mut LeanObject;
pub static l_reduceCtorEq___closed__3_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_reduceCtorEq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___closed__3_value) as *mut LeanObject;
pub static l_reduceCtorEq___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_reduceCtorEq___closed__3_value) as *mut LeanObject,
        8738205681931236784 as *mut LeanObject,
    ],
};
static mut l_reduceCtorEq___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___closed__4_value) as *mut LeanObject;
pub static l_reduceCtorEq___boxed__const__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [3 as *mut LeanObject],
};
pub static mut l_reduceCtorEq___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_reduceCtorEq___boxed__const__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut LeanObject,233589347272681201 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_reduceCtorEq___closed__2_value) as *mut LeanObject,((( 3 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value: LeanArrayObject<4> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_reduceIte(
    mut v_e_1207_: *mut LeanObject,
    mut v_a_1208_: *mut LeanObject,
    mut v_a_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
    mut v_a_1211_: *mut LeanObject,
    mut v_a_1212_: *mut LeanObject,
    mut v_a_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v_arg_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    let mut v_arg_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: u8 = 0;
    let mut v_arg_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v_arg_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut v_arg_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: u8 = 0;
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v_expr_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: u8 = 0;
    let mut v___x_1251_: u8 = 0;
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_a_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1280_: u8 = 0;
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1285_: u8 = 0;
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut v_a_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1305_: u8 = 0;
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_a_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1310_: u8 = 0;
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1314_: u8 = 0;
    let mut v_isSharedCheck_1315_: u8 = 0;
    let mut v_a_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1216_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1207_, v_a_1212_);
                if lean_obj_tag(v___x_1216_) == 0 {
                    v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
                    v_isSharedCheck_1315_ = (!lean_is_exclusive(v___x_1216_)) as u8;
                    if v_isSharedCheck_1315_ == 0 {
                        v___x_1219_ = v___x_1216_;
                        v_isShared_1220_ = v_isSharedCheck_1315_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1217_);
                        lean_dec(v___x_1216_);
                        v___x_1219_ = lean_box(0);
                        v_isShared_1220_ = v_isSharedCheck_1315_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1316_ = lean_ctor_get(v___x_1216_, 0);
                    v_isSharedCheck_1323_ = (!lean_is_exclusive(v___x_1216_)) as u8;
                    if v_isSharedCheck_1323_ == 0 {
                        v___x_1318_ = v___x_1216_;
                        v_isShared_1319_ = v_isSharedCheck_1323_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_1316_);
                        lean_dec(v___x_1216_);
                        v___x_1318_ = lean_box(0);
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
                    lean_dec_ref(v___x_1226_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1228_ = lean_ctor_get(v___x_1226_, 1);
                    lean_inc_ref(v_arg_1228_);
                    v___x_1229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1226_);
                    v___x_1230_ = l_Lean_Expr_isApp(v___x_1229_);
                    if v___x_1230_ == 0 {
                        lean_dec_ref(v___x_1229_);
                        lean_dec_ref(v_arg_1228_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_1231_ = lean_ctor_get(v___x_1229_, 1);
                        lean_inc_ref(v_arg_1231_);
                        v___x_1232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1229_);
                        v___x_1233_ = l_Lean_Expr_isApp(v___x_1232_);
                        if v___x_1233_ == 0 {
                            lean_dec_ref(v___x_1232_);
                            lean_dec_ref(v_arg_1231_);
                            lean_dec_ref(v_arg_1228_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_1234_ = lean_ctor_get(v___x_1232_, 1);
                            lean_inc_ref(v_arg_1234_);
                            v___x_1235_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1232_);
                            v___x_1236_ = l_Lean_Expr_isApp(v___x_1235_);
                            if v___x_1236_ == 0 {
                                lean_dec_ref(v___x_1235_);
                                lean_dec_ref(v_arg_1234_);
                                lean_dec_ref(v_arg_1231_);
                                lean_dec_ref(v_arg_1228_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_1237_ = lean_ctor_get(v___x_1235_, 1);
                                lean_inc_ref(v_arg_1237_);
                                v___x_1238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1235_);
                                v___x_1239_ = l_Lean_Expr_isApp(v___x_1238_);
                                if v___x_1239_ == 0 {
                                    lean_dec_ref(v___x_1238_);
                                    lean_dec_ref(v_arg_1237_);
                                    lean_dec_ref(v_arg_1234_);
                                    lean_dec_ref(v_arg_1231_);
                                    lean_dec_ref(v_arg_1228_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_1240_ = lean_ctor_get(v___x_1238_, 1);
                                    lean_inc_ref(v_arg_1240_);
                                    v___x_1241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1238_);
                                    v___x_1242_ = l_reduceIte___closed__2;
                                    v___x_1243_ = l_Lean_Expr_isConstOf(v___x_1241_, v___x_1242_);
                                    if v___x_1243_ == 0 {
                                        lean_dec_ref(v___x_1241_);
                                        lean_dec_ref(v_arg_1240_);
                                        lean_dec_ref(v_arg_1237_);
                                        lean_dec_ref(v_arg_1234_);
                                        lean_dec_ref(v_arg_1231_);
                                        lean_dec_ref(v_arg_1228_);
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_del_object(v___x_1219_);
                                        lean_inc(v_a_1214_);
                                        lean_inc_ref(v_a_1213_);
                                        lean_inc(v_a_1212_);
                                        lean_inc_ref(v_a_1211_);
                                        lean_inc(v_a_1210_);
                                        lean_inc_ref(v_a_1209_);
                                        lean_inc(v_a_1208_);
                                        lean_inc_ref(v_arg_1237_);
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
                                        if lean_obj_tag(v___x_1244_) == 0 {
                                            v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
                                            v_isSharedCheck_1306_ =
                                                (!lean_is_exclusive(v___x_1244_)) as u8;
                                            if v_isSharedCheck_1306_ == 0 {
                                                v___x_1247_ = v___x_1244_;
                                                v_isShared_1248_ = v_isSharedCheck_1306_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1245_);
                                                lean_dec(v___x_1244_);
                                                v___x_1247_ = lean_box(0);
                                                v_isShared_1248_ = v_isSharedCheck_1306_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_1241_);
                                            lean_dec_ref(v_arg_1240_);
                                            lean_dec_ref(v_arg_1237_);
                                            lean_dec_ref(v_arg_1234_);
                                            lean_dec_ref(v_arg_1231_);
                                            lean_dec_ref(v_arg_1228_);
                                            v_a_1307_ = lean_ctor_get(v___x_1244_, 0);
                                            v_isSharedCheck_1314_ =
                                                (!lean_is_exclusive(v___x_1244_)) as u8;
                                            if v_isSharedCheck_1314_ == 0 {
                                                v___x_1309_ = v___x_1244_;
                                                v_isShared_1310_ = v_isSharedCheck_1314_;
                                                state = 14;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1307_);
                                                lean_dec(v___x_1244_);
                                                v___x_1309_ = lean_box(0);
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
                    lean_ctor_set(v___x_1219_, 0, v___x_1222_);
                    v___x_1224_ = v___x_1219_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1224_;
            }
            4 => {
                v_expr_1249_ = lean_ctor_get(v_a_1245_, 0);
                lean_inc_ref(v_expr_1249_);
                v___x_1250_ = l_Lean_Expr_isTrue(v_expr_1249_);
                if v___x_1250_ == 0 {
                    lean_inc_ref(v_expr_1249_);
                    v___x_1251_ = l_Lean_Expr_isFalse(v_expr_1249_);
                    if v___x_1251_ == 0 {
                        lean_dec(v_a_1245_);
                        lean_dec_ref(v___x_1241_);
                        lean_dec_ref(v_arg_1240_);
                        lean_dec_ref(v_arg_1237_);
                        lean_dec_ref(v_arg_1234_);
                        lean_dec_ref(v_arg_1231_);
                        lean_dec_ref(v_arg_1228_);
                        v___x_1252_ = l_reduceIte___closed__0;
                        if v_isShared_1248_ == 0 {
                            lean_ctor_set(v___x_1247_, 0, v___x_1252_);
                            v___x_1254_ = v___x_1247_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
                            v___x_1254_ = v_reuseFailAlloc_1255_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1247_);
                        v___x_1256_ = l_Lean_Meta_Simp_Result_getProof(
                            v_a_1245_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_,
                        );
                        if lean_obj_tag(v___x_1256_) == 0 {
                            v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
                            v_isSharedCheck_1272_ = (!lean_is_exclusive(v___x_1256_)) as u8;
                            if v_isSharedCheck_1272_ == 0 {
                                v___x_1259_ = v___x_1256_;
                                v_isShared_1260_ = v_isSharedCheck_1272_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1257_);
                                lean_dec(v___x_1256_);
                                v___x_1259_ = lean_box(0);
                                v_isShared_1260_ = v_isSharedCheck_1272_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1241_);
                            lean_dec_ref(v_arg_1240_);
                            lean_dec_ref(v_arg_1237_);
                            lean_dec_ref(v_arg_1234_);
                            lean_dec_ref(v_arg_1231_);
                            lean_dec_ref(v_arg_1228_);
                            v_a_1273_ = lean_ctor_get(v___x_1256_, 0);
                            v_isSharedCheck_1280_ = (!lean_is_exclusive(v___x_1256_)) as u8;
                            if v_isSharedCheck_1280_ == 0 {
                                v___x_1275_ = v___x_1256_;
                                v_isShared_1276_ = v_isSharedCheck_1280_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_1273_);
                                lean_dec(v___x_1256_);
                                v___x_1275_ = lean_box(0);
                                v_isShared_1276_ = v_isSharedCheck_1280_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_1247_);
                    v___x_1281_ = l_Lean_Meta_Simp_Result_getProof(
                        v_a_1245_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_,
                    );
                    if lean_obj_tag(v___x_1281_) == 0 {
                        v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
                        v_isSharedCheck_1297_ = (!lean_is_exclusive(v___x_1281_)) as u8;
                        if v_isSharedCheck_1297_ == 0 {
                            v___x_1284_ = v___x_1281_;
                            v_isShared_1285_ = v_isSharedCheck_1297_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1282_);
                            lean_dec(v___x_1281_);
                            v___x_1284_ = lean_box(0);
                            v_isShared_1285_ = v_isSharedCheck_1297_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1241_);
                        lean_dec_ref(v_arg_1240_);
                        lean_dec_ref(v_arg_1237_);
                        lean_dec_ref(v_arg_1234_);
                        lean_dec_ref(v_arg_1231_);
                        lean_dec_ref(v_arg_1228_);
                        v_a_1298_ = lean_ctor_get(v___x_1281_, 0);
                        v_isSharedCheck_1305_ = (!lean_is_exclusive(v___x_1281_)) as u8;
                        if v_isSharedCheck_1305_ == 0 {
                            v___x_1300_ = v___x_1281_;
                            v_isShared_1301_ = v_isSharedCheck_1305_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_1298_);
                            lean_dec(v___x_1281_);
                            v___x_1300_ = lean_box(0);
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
                lean_dec_ref(v___x_1241_);
                v___x_1263_ = l_Lean_mkConst(v___x_1261_, v___x_1262_);
                lean_inc_ref(v_arg_1228_);
                v___x_1264_ = l_Lean_mkApp5(
                    v___x_1263_,
                    v_arg_1240_,
                    v_arg_1237_,
                    v_arg_1234_,
                    v_arg_1231_,
                    v_arg_1228_,
                );
                v___x_1265_ = l_Lean_Expr_app___override(v___x_1264_, v_a_1257_);
                v___x_1266_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1266_, 0, v___x_1265_);
                v___x_1267_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_1267_, 0, v_arg_1228_);
                lean_ctor_set(v___x_1267_, 1, v___x_1266_);
                lean_ctor_set_uint8(
                    v___x_1267_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_1243_,
                );
                v___x_1268_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1268_, 0, v___x_1267_);
                if v_isShared_1260_ == 0 {
                    lean_ctor_set(v___x_1259_, 0, v___x_1268_);
                    v___x_1270_ = v___x_1259_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1268_);
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
                    v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
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
                lean_dec_ref(v___x_1241_);
                v___x_1288_ = l_Lean_mkConst(v___x_1286_, v___x_1287_);
                lean_inc_ref(v_arg_1231_);
                v___x_1289_ = l_Lean_mkApp5(
                    v___x_1288_,
                    v_arg_1240_,
                    v_arg_1237_,
                    v_arg_1234_,
                    v_arg_1231_,
                    v_arg_1228_,
                );
                v___x_1290_ = l_Lean_Expr_app___override(v___x_1289_, v_a_1282_);
                v___x_1291_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1291_, 0, v___x_1290_);
                v___x_1292_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_1292_, 0, v_arg_1231_);
                lean_ctor_set(v___x_1292_, 1, v___x_1291_);
                lean_ctor_set_uint8(
                    v___x_1292_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_1243_,
                );
                v___x_1293_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1293_, 0, v___x_1292_);
                if v_isShared_1285_ == 0 {
                    lean_ctor_set(v___x_1284_, 0, v___x_1293_);
                    v___x_1295_ = v___x_1284_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
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
                    v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
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
                    v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
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
                    v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
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
    mut v_e_1324_: *mut LeanObject,
    mut v_a_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
    mut v_a_1327_: *mut LeanObject,
    mut v_a_1328_: *mut LeanObject,
    mut v_a_1329_: *mut LeanObject,
    mut v_a_1330_: *mut LeanObject,
    mut v_a_1331_: *mut LeanObject,
    mut v_a_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1333_: *mut LeanObject = core::ptr::null_mut();
    v_res_1333_ = l_reduceIte(
        v_e_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_,
    );
    lean_dec(v_a_1331_);
    lean_dec_ref(v_a_1330_);
    lean_dec(v_a_1329_);
    lean_dec_ref(v_a_1328_);
    lean_dec(v_a_1327_);
    lean_dec_ref(v_a_1326_);
    lean_dec(v_a_1325_);
    return v_res_1333_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1352_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1353_ = lean_alloc_closure(l_reduceIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1354_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1351_, v___x_1352_, v___x_1353_);
    return v___x_1354_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15____boxed(
    mut v_a_1355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1356_: *mut LeanObject = core::ptr::null_mut();
    v_res_1356_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
    return v_res_1356_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    v___x_1357_ = lean_alloc_closure(l_reduceIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1358_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1358_, 0, v___x_1357_);
    return v___x_1358_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1361_ = 0;
    v___x_1362_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
    v___x_1363_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1360_, v___x_1361_, v___x_1362_);
    return v___x_1363_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17____boxed(
    mut v_a_1364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1365_: *mut LeanObject = core::ptr::null_mut();
    v_res_1365_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
    return v_res_1365_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_()
-> *mut LeanObject {
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    v___x_1367_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1368_ = 0;
    v___x_1369_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_);
    v___x_1370_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1367_, v___x_1368_, v___x_1369_);
    return v___x_1370_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19____boxed(
    mut v_a_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1372_: *mut LeanObject = core::ptr::null_mut();
    v_res_1372_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
    return v_res_1372_;
}
pub unsafe fn _init_l_reduceDIte___closed__4() -> *mut LeanObject {
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    v___x_1379_ = lean_box(0);
    v___x_1380_ = l_reduceDIte___closed__3;
    v___x_1381_ = l_Lean_mkConst(v___x_1380_, v___x_1379_);
    return v___x_1381_;
}
pub unsafe fn _init_l_reduceDIte___closed__9() -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = lean_box(0);
    v___x_1389_ = l_reduceDIte___closed__8;
    v___x_1390_ = l_Lean_mkConst(v___x_1389_, v___x_1388_);
    return v___x_1390_;
}
pub unsafe fn l_reduceDIte(
    mut v_e_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
    mut v_a_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v_arg_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v_arg_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v_arg_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: u8 = 0;
    let mut v_arg_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut v_arg_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v_expr_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1447_: u8 = 0;
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1463_: u8 = 0;
    let mut v_a_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1467_: u8 = 0;
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1476_: u8 = 0;
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_a_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1500_: u8 = 0;
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_a_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut v_a_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1403_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1394_, v_a_1399_);
                if lean_obj_tag(v___x_1403_) == 0 {
                    v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
                    v_isSharedCheck_1510_ = (!lean_is_exclusive(v___x_1403_)) as u8;
                    if v_isSharedCheck_1510_ == 0 {
                        v___x_1406_ = v___x_1403_;
                        v_isShared_1407_ = v_isSharedCheck_1510_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1404_);
                        lean_dec(v___x_1403_);
                        v___x_1406_ = lean_box(0);
                        v_isShared_1407_ = v_isSharedCheck_1510_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1511_ = lean_ctor_get(v___x_1403_, 0);
                    v_isSharedCheck_1518_ = (!lean_is_exclusive(v___x_1403_)) as u8;
                    if v_isSharedCheck_1518_ == 0 {
                        v___x_1513_ = v___x_1403_;
                        v_isShared_1514_ = v_isSharedCheck_1518_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_1511_);
                        lean_dec(v___x_1403_);
                        v___x_1513_ = lean_box(0);
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
                    lean_dec_ref(v___x_1413_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1415_ = lean_ctor_get(v___x_1413_, 1);
                    lean_inc_ref(v_arg_1415_);
                    v___x_1416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1413_);
                    v___x_1417_ = l_Lean_Expr_isApp(v___x_1416_);
                    if v___x_1417_ == 0 {
                        lean_dec_ref(v___x_1416_);
                        lean_dec_ref(v_arg_1415_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_1418_ = lean_ctor_get(v___x_1416_, 1);
                        lean_inc_ref(v_arg_1418_);
                        v___x_1419_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1416_);
                        v___x_1420_ = l_Lean_Expr_isApp(v___x_1419_);
                        if v___x_1420_ == 0 {
                            lean_dec_ref(v___x_1419_);
                            lean_dec_ref(v_arg_1418_);
                            lean_dec_ref(v_arg_1415_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_1421_ = lean_ctor_get(v___x_1419_, 1);
                            lean_inc_ref(v_arg_1421_);
                            v___x_1422_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1419_);
                            v___x_1423_ = l_Lean_Expr_isApp(v___x_1422_);
                            if v___x_1423_ == 0 {
                                lean_dec_ref(v___x_1422_);
                                lean_dec_ref(v_arg_1421_);
                                lean_dec_ref(v_arg_1418_);
                                lean_dec_ref(v_arg_1415_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_1424_ = lean_ctor_get(v___x_1422_, 1);
                                lean_inc_ref(v_arg_1424_);
                                v___x_1425_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1422_);
                                v___x_1426_ = l_Lean_Expr_isApp(v___x_1425_);
                                if v___x_1426_ == 0 {
                                    lean_dec_ref(v___x_1425_);
                                    lean_dec_ref(v_arg_1424_);
                                    lean_dec_ref(v_arg_1421_);
                                    lean_dec_ref(v_arg_1418_);
                                    lean_dec_ref(v_arg_1415_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_1427_ = lean_ctor_get(v___x_1425_, 1);
                                    lean_inc_ref(v_arg_1427_);
                                    v___x_1428_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1425_);
                                    v___x_1429_ = l_reduceDIte___closed__1;
                                    v___x_1430_ = l_Lean_Expr_isConstOf(v___x_1428_, v___x_1429_);
                                    if v___x_1430_ == 0 {
                                        lean_dec_ref(v___x_1428_);
                                        lean_dec_ref(v_arg_1427_);
                                        lean_dec_ref(v_arg_1424_);
                                        lean_dec_ref(v_arg_1421_);
                                        lean_dec_ref(v_arg_1418_);
                                        lean_dec_ref(v_arg_1415_);
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_del_object(v___x_1406_);
                                        lean_inc(v_a_1401_);
                                        lean_inc_ref(v_a_1400_);
                                        lean_inc(v_a_1399_);
                                        lean_inc_ref(v_a_1398_);
                                        lean_inc(v_a_1397_);
                                        lean_inc_ref(v_a_1396_);
                                        lean_inc(v_a_1395_);
                                        lean_inc_ref(v_arg_1424_);
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
                                        if lean_obj_tag(v___x_1431_) == 0 {
                                            v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
                                            v_isSharedCheck_1501_ =
                                                (!lean_is_exclusive(v___x_1431_)) as u8;
                                            if v_isSharedCheck_1501_ == 0 {
                                                v___x_1434_ = v___x_1431_;
                                                v_isShared_1435_ = v_isSharedCheck_1501_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1432_);
                                                lean_dec(v___x_1431_);
                                                v___x_1434_ = lean_box(0);
                                                v_isShared_1435_ = v_isSharedCheck_1501_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_1428_);
                                            lean_dec_ref(v_arg_1427_);
                                            lean_dec_ref(v_arg_1424_);
                                            lean_dec_ref(v_arg_1421_);
                                            lean_dec_ref(v_arg_1418_);
                                            lean_dec_ref(v_arg_1415_);
                                            v_a_1502_ = lean_ctor_get(v___x_1431_, 0);
                                            v_isSharedCheck_1509_ =
                                                (!lean_is_exclusive(v___x_1431_)) as u8;
                                            if v_isSharedCheck_1509_ == 0 {
                                                v___x_1504_ = v___x_1431_;
                                                v_isShared_1505_ = v_isSharedCheck_1509_;
                                                state = 14;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1502_);
                                                lean_dec(v___x_1431_);
                                                v___x_1504_ = lean_box(0);
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
                    lean_ctor_set(v___x_1406_, 0, v___x_1409_);
                    v___x_1411_ = v___x_1406_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
                    v___x_1411_ = v_reuseFailAlloc_1412_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1411_;
            }
            4 => {
                v_expr_1436_ = lean_ctor_get(v_a_1432_, 0);
                lean_inc_ref(v_expr_1436_);
                v___x_1437_ = l_Lean_Expr_isTrue(v_expr_1436_);
                if v___x_1437_ == 0 {
                    lean_inc_ref(v_expr_1436_);
                    v___x_1438_ = l_Lean_Expr_isFalse(v_expr_1436_);
                    if v___x_1438_ == 0 {
                        lean_dec(v_a_1432_);
                        lean_dec_ref(v___x_1428_);
                        lean_dec_ref(v_arg_1427_);
                        lean_dec_ref(v_arg_1424_);
                        lean_dec_ref(v_arg_1421_);
                        lean_dec_ref(v_arg_1418_);
                        lean_dec_ref(v_arg_1415_);
                        v___x_1439_ = l_reduceIte___closed__0;
                        if v_isShared_1435_ == 0 {
                            lean_ctor_set(v___x_1434_, 0, v___x_1439_);
                            v___x_1441_ = v___x_1434_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
                            v___x_1441_ = v_reuseFailAlloc_1442_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1434_);
                        v___x_1443_ = l_Lean_Meta_Simp_Result_getProof(
                            v_a_1432_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_,
                        );
                        if lean_obj_tag(v___x_1443_) == 0 {
                            v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
                            v_isSharedCheck_1463_ = (!lean_is_exclusive(v___x_1443_)) as u8;
                            if v_isSharedCheck_1463_ == 0 {
                                v___x_1446_ = v___x_1443_;
                                v_isShared_1447_ = v_isSharedCheck_1463_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1444_);
                                lean_dec(v___x_1443_);
                                v___x_1446_ = lean_box(0);
                                v_isShared_1447_ = v_isSharedCheck_1463_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1428_);
                            lean_dec_ref(v_arg_1427_);
                            lean_dec_ref(v_arg_1424_);
                            lean_dec_ref(v_arg_1421_);
                            lean_dec_ref(v_arg_1418_);
                            lean_dec_ref(v_arg_1415_);
                            v_a_1464_ = lean_ctor_get(v___x_1443_, 0);
                            v_isSharedCheck_1471_ = (!lean_is_exclusive(v___x_1443_)) as u8;
                            if v_isSharedCheck_1471_ == 0 {
                                v___x_1466_ = v___x_1443_;
                                v_isShared_1467_ = v_isSharedCheck_1471_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_1464_);
                                lean_dec(v___x_1443_);
                                v___x_1466_ = lean_box(0);
                                v_isShared_1467_ = v_isSharedCheck_1471_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_1434_);
                    v___x_1472_ = l_Lean_Meta_Simp_Result_getProof(
                        v_a_1432_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_,
                    );
                    if lean_obj_tag(v___x_1472_) == 0 {
                        v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
                        v_isSharedCheck_1492_ = (!lean_is_exclusive(v___x_1472_)) as u8;
                        if v_isSharedCheck_1492_ == 0 {
                            v___x_1475_ = v___x_1472_;
                            v_isShared_1476_ = v_isSharedCheck_1492_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1473_);
                            lean_dec(v___x_1472_);
                            v___x_1475_ = lean_box(0);
                            v_isShared_1476_ = v_isSharedCheck_1492_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1428_);
                        lean_dec_ref(v_arg_1427_);
                        lean_dec_ref(v_arg_1424_);
                        lean_dec_ref(v_arg_1421_);
                        lean_dec_ref(v_arg_1418_);
                        lean_dec_ref(v_arg_1415_);
                        v_a_1493_ = lean_ctor_get(v___x_1472_, 0);
                        v_isSharedCheck_1500_ = (!lean_is_exclusive(v___x_1472_)) as u8;
                        if v_isSharedCheck_1500_ == 0 {
                            v___x_1495_ = v___x_1472_;
                            v_isShared_1496_ = v_isSharedCheck_1500_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_1493_);
                            lean_dec(v___x_1472_);
                            v___x_1495_ = lean_box(0);
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
                v___x_1448_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_reduceDIte___closed__4),
                    core::ptr::addr_of_mut!(l_reduceDIte___closed__4_once),
                    _init_l_reduceDIte___closed__4,
                );
                lean_inc(v_a_1444_);
                lean_inc_ref(v_arg_1424_);
                v___x_1449_ = l_Lean_mkAppB(v___x_1448_, v_arg_1424_, v_a_1444_);
                lean_inc_ref(v_arg_1415_);
                v___x_1450_ = l_Lean_Expr_app___override(v_arg_1415_, v___x_1449_);
                v___x_1451_ = l_Lean_Expr_headBeta(v___x_1450_);
                v___x_1452_ = l_reduceDIte___closed__6;
                v___x_1453_ = l_Lean_Expr_constLevels_x21(v___x_1428_);
                lean_dec_ref(v___x_1428_);
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
                v___x_1457_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1457_, 0, v___x_1456_);
                v___x_1458_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_1458_, 0, v___x_1451_);
                lean_ctor_set(v___x_1458_, 1, v___x_1457_);
                lean_ctor_set_uint8(
                    v___x_1458_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_1430_,
                );
                v___x_1459_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1459_, 0, v___x_1458_);
                if v_isShared_1447_ == 0 {
                    lean_ctor_set(v___x_1446_, 0, v___x_1459_);
                    v___x_1461_ = v___x_1446_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
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
                    v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
                    v___x_1469_ = v_reuseFailAlloc_1470_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1469_;
            }
            10 => {
                v___x_1477_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_reduceDIte___closed__9),
                    core::ptr::addr_of_mut!(l_reduceDIte___closed__9_once),
                    _init_l_reduceDIte___closed__9,
                );
                lean_inc(v_a_1473_);
                lean_inc_ref(v_arg_1424_);
                v___x_1478_ = l_Lean_mkAppB(v___x_1477_, v_arg_1424_, v_a_1473_);
                lean_inc_ref(v_arg_1418_);
                v___x_1479_ = l_Lean_Expr_app___override(v_arg_1418_, v___x_1478_);
                v___x_1480_ = l_Lean_Expr_headBeta(v___x_1479_);
                v___x_1481_ = l_reduceDIte___closed__11;
                v___x_1482_ = l_Lean_Expr_constLevels_x21(v___x_1428_);
                lean_dec_ref(v___x_1428_);
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
                v___x_1486_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1486_, 0, v___x_1485_);
                v___x_1487_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_1487_, 0, v___x_1480_);
                lean_ctor_set(v___x_1487_, 1, v___x_1486_);
                lean_ctor_set_uint8(
                    v___x_1487_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_1430_,
                );
                v___x_1488_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1488_, 0, v___x_1487_);
                if v_isShared_1476_ == 0 {
                    lean_ctor_set(v___x_1475_, 0, v___x_1488_);
                    v___x_1490_ = v___x_1475_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
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
                    v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
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
                    v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
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
                    v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
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
    mut v_e_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
    mut v_a_1522_: *mut LeanObject,
    mut v_a_1523_: *mut LeanObject,
    mut v_a_1524_: *mut LeanObject,
    mut v_a_1525_: *mut LeanObject,
    mut v_a_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1528_: *mut LeanObject = core::ptr::null_mut();
    v_res_1528_ = l_reduceDIte(
        v_e_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_,
    );
    lean_dec(v_a_1526_);
    lean_dec_ref(v_a_1525_);
    lean_dec(v_a_1524_);
    lean_dec_ref(v_a_1523_);
    lean_dec(v_a_1522_);
    lean_dec_ref(v_a_1521_);
    lean_dec(v_a_1520_);
    return v_res_1528_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    v___x_1546_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1547_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1548_ = lean_alloc_closure(l_reduceDIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1549_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_1546_, v___x_1547_, v___x_1548_);
    return v___x_1549_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15____boxed(
    mut v_a_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1551_: *mut LeanObject = core::ptr::null_mut();
    v_res_1551_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
    return v_res_1551_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v___x_1552_ = lean_alloc_closure(l_reduceDIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1553_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1553_, 0, v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    v___x_1555_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1556_ = 0;
    v___x_1557_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
    v___x_1558_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1555_, v___x_1556_, v___x_1557_);
    return v___x_1558_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17____boxed(
    mut v_a_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1560_: *mut LeanObject = core::ptr::null_mut();
    v_res_1560_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
    return v_res_1560_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_()
-> *mut LeanObject {
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    v___x_1562_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1563_ = 0;
    v___x_1564_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_);
    v___x_1565_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1562_, v___x_1563_, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19____boxed(
    mut v_a_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1567_: *mut LeanObject = core::ptr::null_mut();
    v_res_1567_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
    return v_res_1567_;
}
pub unsafe fn l_dreduceIte(
    mut v_e_1579_: *mut LeanObject,
    mut v_a_1580_: *mut LeanObject,
    mut v_a_1581_: *mut LeanObject,
    mut v_a_1582_: *mut LeanObject,
    mut v_a_1583_: *mut LeanObject,
    mut v_a_1584_: *mut LeanObject,
    mut v_a_1585_: *mut LeanObject,
    mut v_a_1586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inDSimp_1591_: u8 = 0;
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1598_: u8 = 0;
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v_arg_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: u8 = 0;
    let mut v_arg_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v_arg_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v_arg_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v_a_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v_a_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_expr_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut v_a_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1679_: u8 = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_a_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inDSimp_1591_ = lean_ctor_get_uint8(
                    v_a_1581_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 8) as u32,
                );
                if v_inDSimp_1591_ == 0 {
                    lean_dec_ref(v_e_1579_);
                    v___x_1592_ = l_dreduceIte___closed__0;
                    v___x_1593_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1593_, 0, v___x_1592_);
                    return v___x_1593_;
                } else {
                    v___x_1594_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1579_, v_a_1584_);
                    if lean_obj_tag(v___x_1594_) == 0 {
                        v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
                        v_isSharedCheck_1684_ = (!lean_is_exclusive(v___x_1594_)) as u8;
                        if v_isSharedCheck_1684_ == 0 {
                            v___x_1597_ = v___x_1594_;
                            v_isShared_1598_ = v_isSharedCheck_1684_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1595_);
                            lean_dec(v___x_1594_);
                            v___x_1597_ = lean_box(0);
                            v_isShared_1598_ = v_isSharedCheck_1684_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1685_ = lean_ctor_get(v___x_1594_, 0);
                        v_isSharedCheck_1692_ = (!lean_is_exclusive(v___x_1594_)) as u8;
                        if v_isSharedCheck_1692_ == 0 {
                            v___x_1687_ = v___x_1594_;
                            v_isShared_1688_ = v_isSharedCheck_1692_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_1685_);
                            lean_dec(v___x_1594_);
                            v___x_1687_ = lean_box(0);
                            v_isShared_1688_ = v_isSharedCheck_1692_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1589_ = l_dreduceIte___closed__0;
                v___x_1590_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1590_, 0, v___x_1589_);
                return v___x_1590_;
            }
            2 => {
                v___x_1604_ = l_Lean_Expr_cleanupAnnotations(v_a_1595_);
                v___x_1605_ = l_Lean_Expr_isApp(v___x_1604_);
                if v___x_1605_ == 0 {
                    lean_dec_ref(v___x_1604_);
                    state = 3;
                    continue;
                } else {
                    v_arg_1606_ = lean_ctor_get(v___x_1604_, 1);
                    lean_inc_ref(v_arg_1606_);
                    v___x_1607_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1604_);
                    v___x_1608_ = l_Lean_Expr_isApp(v___x_1607_);
                    if v___x_1608_ == 0 {
                        lean_dec_ref(v___x_1607_);
                        lean_dec_ref(v_arg_1606_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_1609_ = lean_ctor_get(v___x_1607_, 1);
                        lean_inc_ref(v_arg_1609_);
                        v___x_1610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1607_);
                        v___x_1611_ = l_Lean_Expr_isApp(v___x_1610_);
                        if v___x_1611_ == 0 {
                            lean_dec_ref(v___x_1610_);
                            lean_dec_ref(v_arg_1609_);
                            lean_dec_ref(v_arg_1606_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_1612_ = lean_ctor_get(v___x_1610_, 1);
                            lean_inc_ref(v_arg_1612_);
                            v___x_1613_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1610_);
                            v___x_1614_ = l_Lean_Expr_isApp(v___x_1613_);
                            if v___x_1614_ == 0 {
                                lean_dec_ref(v___x_1613_);
                                lean_dec_ref(v_arg_1612_);
                                lean_dec_ref(v_arg_1609_);
                                lean_dec_ref(v_arg_1606_);
                                state = 3;
                                continue;
                            } else {
                                v_arg_1615_ = lean_ctor_get(v___x_1613_, 1);
                                lean_inc_ref(v_arg_1615_);
                                v___x_1616_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1613_);
                                v___x_1617_ = l_Lean_Expr_isApp(v___x_1616_);
                                if v___x_1617_ == 0 {
                                    lean_dec_ref(v___x_1616_);
                                    lean_dec_ref(v_arg_1615_);
                                    lean_dec_ref(v_arg_1612_);
                                    lean_dec_ref(v_arg_1609_);
                                    lean_dec_ref(v_arg_1606_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_1618_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1616_);
                                    v___x_1619_ = l_reduceIte___closed__2;
                                    v___x_1620_ = l_Lean_Expr_isConstOf(v___x_1618_, v___x_1619_);
                                    lean_dec_ref(v___x_1618_);
                                    if v___x_1620_ == 0 {
                                        lean_dec_ref(v_arg_1615_);
                                        lean_dec_ref(v_arg_1612_);
                                        lean_dec_ref(v_arg_1609_);
                                        lean_dec_ref(v_arg_1606_);
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_del_object(v___x_1597_);
                                        lean_inc(v_a_1586_);
                                        lean_inc_ref(v_a_1585_);
                                        lean_inc(v_a_1584_);
                                        lean_inc_ref(v_a_1583_);
                                        lean_inc(v_a_1582_);
                                        lean_inc_ref(v_a_1581_);
                                        lean_inc(v_a_1580_);
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
                                        if lean_obj_tag(v___x_1621_) == 0 {
                                            v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
                                            v_isSharedCheck_1675_ =
                                                (!lean_is_exclusive(v___x_1621_)) as u8;
                                            if v_isSharedCheck_1675_ == 0 {
                                                v___x_1624_ = v___x_1621_;
                                                v_isShared_1625_ = v_isSharedCheck_1675_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1622_);
                                                lean_dec(v___x_1621_);
                                                v___x_1624_ = lean_box(0);
                                                v_isShared_1625_ = v_isSharedCheck_1675_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_1612_);
                                            lean_dec_ref(v_arg_1609_);
                                            lean_dec_ref(v_arg_1606_);
                                            v_a_1676_ = lean_ctor_get(v___x_1621_, 0);
                                            v_isSharedCheck_1683_ =
                                                (!lean_is_exclusive(v___x_1621_)) as u8;
                                            if v_isSharedCheck_1683_ == 0 {
                                                v___x_1678_ = v___x_1621_;
                                                v_isShared_1679_ = v_isSharedCheck_1683_;
                                                state = 15;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1676_);
                                                lean_dec(v___x_1621_);
                                                v___x_1678_ = lean_box(0);
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
                    lean_ctor_set(v___x_1597_, 0, v___x_1600_);
                    v___x_1602_ = v___x_1597_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
                    v___x_1602_ = v_reuseFailAlloc_1603_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1602_;
            }
            5 => {
                v_expr_1668_ = lean_ctor_get(v_a_1622_, 0);
                lean_inc_ref_n(v_expr_1668_, 2);
                lean_dec(v_a_1622_);
                v___x_1669_ = l_Lean_Expr_isTrue(v_expr_1668_);
                if v___x_1669_ == 0 {
                    v___x_1670_ = l_Lean_Expr_isFalse(v_expr_1668_);
                    if v___x_1670_ == 0 {
                        lean_dec_ref(v_arg_1612_);
                        lean_dec_ref(v_arg_1609_);
                        lean_dec_ref(v_arg_1606_);
                        v___x_1671_ = l_dreduceIte___closed__0;
                        if v_isShared_1625_ == 0 {
                            lean_ctor_set(v___x_1624_, 0, v___x_1671_);
                            v___x_1673_ = v___x_1624_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
                            v___x_1673_ = v_reuseFailAlloc_1674_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1624_);
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_expr_1668_);
                    lean_del_object(v___x_1624_);
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1627_ =
                    l_Lean_Meta_whnfD(v_arg_1612_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
                if lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
                    lean_inc(v_a_1628_);
                    lean_dec_ref_known(v___x_1627_, 1);
                    v___x_1629_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_1628_, v_a_1584_);
                    if lean_obj_tag(v___x_1629_) == 0 {
                        v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
                        v_isSharedCheck_1651_ = (!lean_is_exclusive(v___x_1629_)) as u8;
                        if v_isSharedCheck_1651_ == 0 {
                            v___x_1632_ = v___x_1629_;
                            v_isShared_1633_ = v_isSharedCheck_1651_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1630_);
                            lean_dec(v___x_1629_);
                            v___x_1632_ = lean_box(0);
                            v_isShared_1633_ = v_isSharedCheck_1651_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_1609_);
                        lean_dec_ref(v_arg_1606_);
                        v_a_1652_ = lean_ctor_get(v___x_1629_, 0);
                        v_isSharedCheck_1659_ = (!lean_is_exclusive(v___x_1629_)) as u8;
                        if v_isSharedCheck_1659_ == 0 {
                            v___x_1654_ = v___x_1629_;
                            v_isShared_1655_ = v_isSharedCheck_1659_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1652_);
                            lean_dec(v___x_1629_);
                            v___x_1654_ = lean_box(0);
                            v_isShared_1655_ = v_isSharedCheck_1659_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_arg_1609_);
                    lean_dec_ref(v_arg_1606_);
                    v_a_1660_ = lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1667_ = (!lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1662_ = v___x_1627_;
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1660_);
                        lean_dec(v___x_1627_);
                        v___x_1662_ = lean_box(0);
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
                    lean_dec_ref(v___x_1634_);
                    lean_del_object(v___x_1632_);
                    lean_dec_ref(v_arg_1609_);
                    lean_dec_ref(v_arg_1606_);
                    state = 1;
                    continue;
                } else {
                    v___x_1636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1634_);
                    v___x_1637_ = l_Lean_Expr_isApp(v___x_1636_);
                    if v___x_1637_ == 0 {
                        lean_dec_ref(v___x_1636_);
                        lean_del_object(v___x_1632_);
                        lean_dec_ref(v_arg_1609_);
                        lean_dec_ref(v_arg_1606_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1636_);
                        v___x_1639_ = l_dreduceIte___closed__3;
                        v___x_1640_ = l_Lean_Expr_isConstOf(v___x_1638_, v___x_1639_);
                        if v___x_1640_ == 0 {
                            lean_dec_ref(v_arg_1606_);
                            v___x_1641_ = l_dreduceIte___closed__5;
                            v___x_1642_ = l_Lean_Expr_isConstOf(v___x_1638_, v___x_1641_);
                            lean_dec_ref(v___x_1638_);
                            if v___x_1642_ == 0 {
                                lean_del_object(v___x_1632_);
                                lean_dec_ref(v_arg_1609_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1643_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1643_, 0, v_arg_1609_);
                                if v_isShared_1633_ == 0 {
                                    lean_ctor_set(v___x_1632_, 0, v___x_1643_);
                                    v___x_1645_ = v___x_1632_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
                                    v___x_1645_ = v_reuseFailAlloc_1646_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_1638_);
                            lean_dec_ref(v_arg_1609_);
                            v___x_1647_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1647_, 0, v_arg_1606_);
                            if v_isShared_1633_ == 0 {
                                lean_ctor_set(v___x_1632_, 0, v___x_1647_);
                                v___x_1649_ = v___x_1632_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
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
                    v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
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
                    v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
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
                    v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
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
                    v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
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
    mut v_e_1693_: *mut LeanObject,
    mut v_a_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
    mut v_a_1696_: *mut LeanObject,
    mut v_a_1697_: *mut LeanObject,
    mut v_a_1698_: *mut LeanObject,
    mut v_a_1699_: *mut LeanObject,
    mut v_a_1700_: *mut LeanObject,
    mut v_a_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1702_: *mut LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_dreduceIte(
        v_e_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_,
    );
    lean_dec(v_a_1700_);
    lean_dec_ref(v_a_1699_);
    lean_dec(v_a_1698_);
    lean_dec_ref(v_a_1697_);
    lean_dec(v_a_1696_);
    lean_dec_ref(v_a_1695_);
    lean_dec(v_a_1694_);
    return v_res_1702_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    v___x_1707_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_;
    v___x_1708_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_;
    v___x_1709_ = lean_alloc_closure(l_dreduceIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1710_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1707_, v___x_1708_, v___x_1709_);
    return v___x_1710_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15____boxed(
    mut v_a_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1712_: *mut LeanObject = core::ptr::null_mut();
    v_res_1712_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
    return v_res_1712_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = lean_alloc_closure(l_dreduceIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1714_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1714_, 0, v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_;
    v___x_1717_ = 0;
    v___x_1718_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_);
    v___x_1719_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1716_, v___x_1717_, v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17____boxed(
    mut v_a_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1721_: *mut LeanObject = core::ptr::null_mut();
    v_res_1721_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
    return v_res_1721_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_()
-> *mut LeanObject {
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    v___x_1723_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_;
    v___x_1724_ = 0;
    v___x_1725_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_);
    v___x_1726_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1723_, v___x_1724_, v___x_1725_);
    return v___x_1726_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19____boxed(
    mut v_a_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1728_: *mut LeanObject = core::ptr::null_mut();
    v_res_1728_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
    return v_res_1728_;
}
pub unsafe fn l_dreduceDIte(
    mut v_e_1729_: *mut LeanObject,
    mut v_a_1730_: *mut LeanObject,
    mut v_a_1731_: *mut LeanObject,
    mut v_a_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
    mut v_a_1734_: *mut LeanObject,
    mut v_a_1735_: *mut LeanObject,
    mut v_a_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inDSimp_1741_: u8 = 0;
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v_arg_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v_arg_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v_arg_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v_arg_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v_arg_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_a_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut v_a_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v_expr_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v_a_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut v_a_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inDSimp_1741_ = lean_ctor_get_uint8(
                    v_a_1731_,
                    (core::mem::size_of::<*mut LeanObject>() * 10 + 8) as u32,
                );
                if v_inDSimp_1741_ == 0 {
                    lean_dec_ref(v_e_1729_);
                    v___x_1742_ = l_dreduceIte___closed__0;
                    v___x_1743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                    return v___x_1743_;
                } else {
                    v___x_1744_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1729_, v_a_1734_);
                    if lean_obj_tag(v___x_1744_) == 0 {
                        v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
                        v_isSharedCheck_1839_ = (!lean_is_exclusive(v___x_1744_)) as u8;
                        if v_isSharedCheck_1839_ == 0 {
                            v___x_1747_ = v___x_1744_;
                            v_isShared_1748_ = v_isSharedCheck_1839_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1745_);
                            lean_dec(v___x_1744_);
                            v___x_1747_ = lean_box(0);
                            v_isShared_1748_ = v_isSharedCheck_1839_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1840_ = lean_ctor_get(v___x_1744_, 0);
                        v_isSharedCheck_1847_ = (!lean_is_exclusive(v___x_1744_)) as u8;
                        if v_isSharedCheck_1847_ == 0 {
                            v___x_1842_ = v___x_1744_;
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_1840_);
                            lean_dec(v___x_1744_);
                            v___x_1842_ = lean_box(0);
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1739_ = l_dreduceIte___closed__0;
                v___x_1740_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1740_, 0, v___x_1739_);
                return v___x_1740_;
            }
            2 => {
                v___x_1754_ = l_Lean_Expr_cleanupAnnotations(v_a_1745_);
                v___x_1755_ = l_Lean_Expr_isApp(v___x_1754_);
                if v___x_1755_ == 0 {
                    lean_dec_ref(v___x_1754_);
                    state = 3;
                    continue;
                } else {
                    v_arg_1756_ = lean_ctor_get(v___x_1754_, 1);
                    lean_inc_ref(v_arg_1756_);
                    v___x_1757_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1754_);
                    v___x_1758_ = l_Lean_Expr_isApp(v___x_1757_);
                    if v___x_1758_ == 0 {
                        lean_dec_ref(v___x_1757_);
                        lean_dec_ref(v_arg_1756_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_1759_ = lean_ctor_get(v___x_1757_, 1);
                        lean_inc_ref(v_arg_1759_);
                        v___x_1760_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1757_);
                        v___x_1761_ = l_Lean_Expr_isApp(v___x_1760_);
                        if v___x_1761_ == 0 {
                            lean_dec_ref(v___x_1760_);
                            lean_dec_ref(v_arg_1759_);
                            lean_dec_ref(v_arg_1756_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_1762_ = lean_ctor_get(v___x_1760_, 1);
                            lean_inc_ref(v_arg_1762_);
                            v___x_1763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1760_);
                            v___x_1764_ = l_Lean_Expr_isApp(v___x_1763_);
                            if v___x_1764_ == 0 {
                                lean_dec_ref(v___x_1763_);
                                lean_dec_ref(v_arg_1762_);
                                lean_dec_ref(v_arg_1759_);
                                lean_dec_ref(v_arg_1756_);
                                state = 3;
                                continue;
                            } else {
                                v_arg_1765_ = lean_ctor_get(v___x_1763_, 1);
                                lean_inc_ref(v_arg_1765_);
                                v___x_1766_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1763_);
                                v___x_1767_ = l_Lean_Expr_isApp(v___x_1766_);
                                if v___x_1767_ == 0 {
                                    lean_dec_ref(v___x_1766_);
                                    lean_dec_ref(v_arg_1765_);
                                    lean_dec_ref(v_arg_1762_);
                                    lean_dec_ref(v_arg_1759_);
                                    lean_dec_ref(v_arg_1756_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_1768_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1766_);
                                    v___x_1769_ = l_reduceDIte___closed__1;
                                    v___x_1770_ = l_Lean_Expr_isConstOf(v___x_1768_, v___x_1769_);
                                    lean_dec_ref(v___x_1768_);
                                    if v___x_1770_ == 0 {
                                        lean_dec_ref(v_arg_1765_);
                                        lean_dec_ref(v_arg_1762_);
                                        lean_dec_ref(v_arg_1759_);
                                        lean_dec_ref(v_arg_1756_);
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_del_object(v___x_1747_);
                                        lean_inc(v_a_1736_);
                                        lean_inc_ref(v_a_1735_);
                                        lean_inc(v_a_1734_);
                                        lean_inc_ref(v_a_1733_);
                                        lean_inc(v_a_1732_);
                                        lean_inc_ref(v_a_1731_);
                                        lean_inc(v_a_1730_);
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
                                        if lean_obj_tag(v___x_1771_) == 0 {
                                            v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
                                            v_isSharedCheck_1830_ =
                                                (!lean_is_exclusive(v___x_1771_)) as u8;
                                            if v_isSharedCheck_1830_ == 0 {
                                                v___x_1774_ = v___x_1771_;
                                                v_isShared_1775_ = v_isSharedCheck_1830_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1772_);
                                                lean_dec(v___x_1771_);
                                                v___x_1774_ = lean_box(0);
                                                v_isShared_1775_ = v_isSharedCheck_1830_;
                                                state = 5;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_1762_);
                                            lean_dec_ref(v_arg_1759_);
                                            lean_dec_ref(v_arg_1756_);
                                            v_a_1831_ = lean_ctor_get(v___x_1771_, 0);
                                            v_isSharedCheck_1838_ =
                                                (!lean_is_exclusive(v___x_1771_)) as u8;
                                            if v_isSharedCheck_1838_ == 0 {
                                                v___x_1833_ = v___x_1771_;
                                                v_isShared_1834_ = v_isSharedCheck_1838_;
                                                state = 15;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1831_);
                                                lean_dec(v___x_1771_);
                                                v___x_1833_ = lean_box(0);
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
                    lean_ctor_set(v___x_1747_, 0, v___x_1750_);
                    v___x_1752_ = v___x_1747_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1752_;
            }
            5 => {
                v_expr_1823_ = lean_ctor_get(v_a_1772_, 0);
                lean_inc_ref_n(v_expr_1823_, 2);
                lean_dec(v_a_1772_);
                v___x_1824_ = l_Lean_Expr_isTrue(v_expr_1823_);
                if v___x_1824_ == 0 {
                    v___x_1825_ = l_Lean_Expr_isFalse(v_expr_1823_);
                    if v___x_1825_ == 0 {
                        lean_dec_ref(v_arg_1762_);
                        lean_dec_ref(v_arg_1759_);
                        lean_dec_ref(v_arg_1756_);
                        v___x_1826_ = l_dreduceIte___closed__0;
                        if v_isShared_1775_ == 0 {
                            lean_ctor_set(v___x_1774_, 0, v___x_1826_);
                            v___x_1828_ = v___x_1774_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
                            v___x_1828_ = v_reuseFailAlloc_1829_;
                            state = 14;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1774_);
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_expr_1823_);
                    lean_del_object(v___x_1774_);
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1777_ =
                    l_Lean_Meta_whnfD(v_arg_1762_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
                if lean_obj_tag(v___x_1777_) == 0 {
                    v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
                    lean_inc(v_a_1778_);
                    lean_dec_ref_known(v___x_1777_, 1);
                    v___x_1779_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_1778_, v_a_1734_);
                    if lean_obj_tag(v___x_1779_) == 0 {
                        v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
                        v_isSharedCheck_1806_ = (!lean_is_exclusive(v___x_1779_)) as u8;
                        if v_isSharedCheck_1806_ == 0 {
                            v___x_1782_ = v___x_1779_;
                            v_isShared_1783_ = v_isSharedCheck_1806_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1780_);
                            lean_dec(v___x_1779_);
                            v___x_1782_ = lean_box(0);
                            v_isShared_1783_ = v_isSharedCheck_1806_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_1759_);
                        lean_dec_ref(v_arg_1756_);
                        v_a_1807_ = lean_ctor_get(v___x_1779_, 0);
                        v_isSharedCheck_1814_ = (!lean_is_exclusive(v___x_1779_)) as u8;
                        if v_isSharedCheck_1814_ == 0 {
                            v___x_1809_ = v___x_1779_;
                            v_isShared_1810_ = v_isSharedCheck_1814_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1807_);
                            lean_dec(v___x_1779_);
                            v___x_1809_ = lean_box(0);
                            v_isShared_1810_ = v_isSharedCheck_1814_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_arg_1759_);
                    lean_dec_ref(v_arg_1756_);
                    v_a_1815_ = lean_ctor_get(v___x_1777_, 0);
                    v_isSharedCheck_1822_ = (!lean_is_exclusive(v___x_1777_)) as u8;
                    if v_isSharedCheck_1822_ == 0 {
                        v___x_1817_ = v___x_1777_;
                        v_isShared_1818_ = v_isSharedCheck_1822_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1815_);
                        lean_dec(v___x_1777_);
                        v___x_1817_ = lean_box(0);
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
                    lean_dec_ref(v___x_1784_);
                    lean_del_object(v___x_1782_);
                    lean_dec_ref(v_arg_1759_);
                    lean_dec_ref(v_arg_1756_);
                    state = 1;
                    continue;
                } else {
                    v_arg_1786_ = lean_ctor_get(v___x_1784_, 1);
                    lean_inc_ref(v_arg_1786_);
                    v___x_1787_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1784_);
                    v___x_1788_ = l_Lean_Expr_isApp(v___x_1787_);
                    if v___x_1788_ == 0 {
                        lean_dec_ref(v___x_1787_);
                        lean_dec_ref(v_arg_1786_);
                        lean_del_object(v___x_1782_);
                        lean_dec_ref(v_arg_1759_);
                        lean_dec_ref(v_arg_1756_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1787_);
                        v___x_1790_ = l_dreduceIte___closed__3;
                        v___x_1791_ = l_Lean_Expr_isConstOf(v___x_1789_, v___x_1790_);
                        if v___x_1791_ == 0 {
                            lean_dec_ref(v_arg_1756_);
                            v___x_1792_ = l_dreduceIte___closed__5;
                            v___x_1793_ = l_Lean_Expr_isConstOf(v___x_1789_, v___x_1792_);
                            lean_dec_ref(v___x_1789_);
                            if v___x_1793_ == 0 {
                                lean_dec_ref(v_arg_1786_);
                                lean_del_object(v___x_1782_);
                                lean_dec_ref(v_arg_1759_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1794_ = l_Lean_Expr_app___override(v_arg_1759_, v_arg_1786_);
                                v___x_1795_ = l_Lean_Expr_headBeta(v___x_1794_);
                                v___x_1796_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1796_, 0, v___x_1795_);
                                if v_isShared_1783_ == 0 {
                                    lean_ctor_set(v___x_1782_, 0, v___x_1796_);
                                    v___x_1798_ = v___x_1782_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
                                    v___x_1798_ = v_reuseFailAlloc_1799_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_1789_);
                            lean_dec_ref(v_arg_1759_);
                            v___x_1800_ = l_Lean_Expr_app___override(v_arg_1756_, v_arg_1786_);
                            v___x_1801_ = l_Lean_Expr_headBeta(v___x_1800_);
                            v___x_1802_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1802_, 0, v___x_1801_);
                            if v_isShared_1783_ == 0 {
                                lean_ctor_set(v___x_1782_, 0, v___x_1802_);
                                v___x_1804_ = v___x_1782_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
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
                    v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
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
                    v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
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
                    v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
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
                    v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
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
    mut v_e_1848_: *mut LeanObject,
    mut v_a_1849_: *mut LeanObject,
    mut v_a_1850_: *mut LeanObject,
    mut v_a_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_dreduceDIte(
        v_e_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_,
    );
    lean_dec(v_a_1855_);
    lean_dec_ref(v_a_1854_);
    lean_dec(v_a_1853_);
    lean_dec_ref(v_a_1852_);
    lean_dec(v_a_1851_);
    lean_dec_ref(v_a_1850_);
    lean_dec(v_a_1849_);
    return v_res_1857_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    v___x_1862_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_;
    v___x_1863_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_;
    v___x_1864_ = lean_alloc_closure(l_dreduceDIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1865_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1862_, v___x_1863_, v___x_1864_);
    return v___x_1865_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15____boxed(
    mut v_a_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1867_: *mut LeanObject = core::ptr::null_mut();
    v_res_1867_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
    return v_res_1867_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    v___x_1868_ = lean_alloc_closure(l_dreduceDIte___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_1869_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1869_, 0, v___x_1868_);
    return v___x_1869_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: u8 = 0;
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1871_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_;
    v___x_1872_ = 0;
    v___x_1873_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_);
    v___x_1874_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1871_, v___x_1872_, v___x_1873_);
    return v___x_1874_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17____boxed(
    mut v_a_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1876_: *mut LeanObject = core::ptr::null_mut();
    v_res_1876_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
    return v_res_1876_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_()
-> *mut LeanObject {
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    v___x_1878_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_;
    v___x_1879_ = 0;
    v___x_1880_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_);
    v___x_1881_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_1878_, v___x_1879_, v___x_1880_);
    return v___x_1881_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19____boxed(
    mut v_a_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1883_: *mut LeanObject = core::ptr::null_mut();
    v_res_1883_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
    return v_res_1883_;
}
pub unsafe fn l_reduceCtorEq___lam__0(
    mut v_x_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1893_ = l_reduceIte___closed__0;
    v___x_1894_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1894_, 0, v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn l_reduceCtorEq___lam__0___boxed(
    mut v_x_1895_: *mut LeanObject,
    mut v___y_1896_: *mut LeanObject,
    mut v___y_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
    mut v___y_1903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1904_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1902_);
    lean_dec_ref(v___y_1901_);
    lean_dec(v___y_1900_);
    lean_dec_ref(v___y_1899_);
    lean_dec(v___y_1898_);
    lean_dec_ref(v___y_1897_);
    lean_dec(v___y_1896_);
    return v_res_1904_;
}
pub unsafe fn l_reduceCtorEq___lam__1(
    mut v_x_1905_: *mut LeanObject,
    mut v_x_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
    mut v___y_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    v___x_1915_ = l_reduceIte___closed__0;
    v___x_1916_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1916_, 0, v___x_1915_);
    return v___x_1916_;
}
pub unsafe fn l_reduceCtorEq___lam__1___boxed(
    mut v_x_1917_: *mut LeanObject,
    mut v_x_1918_: *mut LeanObject,
    mut v___y_1919_: *mut LeanObject,
    mut v___y_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1927_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1925_);
    lean_dec_ref(v___y_1924_);
    lean_dec(v___y_1923_);
    lean_dec_ref(v___y_1922_);
    lean_dec(v___y_1921_);
    lean_dec_ref(v___y_1920_);
    lean_dec(v___y_1919_);
    lean_dec(v_x_1918_);
    lean_dec(v_x_1917_);
    return v_res_1927_;
}
pub unsafe fn _init_l_reduceCtorEq___lam__2___closed__2() -> *mut LeanObject {
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    v___x_1931_ = lean_box(0);
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
    mut v_h_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
    mut v___y_1942_: *mut LeanObject,
    mut v___y_1943_: *mut LeanObject,
    mut v___y_1944_: *mut LeanObject,
    mut v___y_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v_trackZetaDelta_1985_: u8 = 0;
    let mut v_zetaDeltaSet_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1992_: u8 = 0;
    let mut v_inTypeClassResolution_1993_: u8 = 0;
    let mut v_cacheInferType_1994_: u8 = 0;
    let mut v___x_1995_: u8 = 0;
    let mut v_config_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: u64 = 0;
    let mut v___x_1999_: u64 = 0;
    let mut v___x_2000_: u64 = 0;
    let mut v___x_2001_: u64 = 0;
    let mut v_key_2002_: u64 = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_a_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_a_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1948_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_reduceCtorEq___lam__2___closed__2),
                    core::ptr::addr_of_mut!(l_reduceCtorEq___lam__2___closed__2_once),
                    _init_l_reduceCtorEq___lam__2___closed__2,
                );
                lean_inc_ref(v_h_1939_);
                v___x_1955_ = l_Lean_Meta_mkNoConfusion(
                    v___x_1948_,
                    v_h_1939_,
                    v___y_1943_,
                    v___y_1944_,
                    v___y_1945_,
                    v___y_1946_,
                );
                if lean_obj_tag(v___x_1955_) == 0 {
                    v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
                    lean_inc(v_a_1956_);
                    lean_dec_ref_known(v___x_1955_, 1);
                    v___x_1957_ = lean_unsigned_to_nat(1);
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
                    lean_dec_ref(v___x_1959_);
                    if lean_obj_tag(v___x_1961_) == 0 {
                        v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
                        lean_inc(v_a_1962_);
                        lean_dec_ref_known(v___x_1961_, 1);
                        v___x_1963_ = l_Lean_Meta_Context_config(v___y_1943_);
                        v_foApprox_1964_ = lean_ctor_get_uint8(v___x_1963_, 0 as u32);
                        v_ctxApprox_1965_ = lean_ctor_get_uint8(v___x_1963_, 1 as u32);
                        v_quasiPatternApprox_1966_ = lean_ctor_get_uint8(v___x_1963_, 2 as u32);
                        v_constApprox_1967_ = lean_ctor_get_uint8(v___x_1963_, 3 as u32);
                        v_isDefEqStuckEx_1968_ = lean_ctor_get_uint8(v___x_1963_, 4 as u32);
                        v_unificationHints_1969_ = lean_ctor_get_uint8(v___x_1963_, 5 as u32);
                        v_proofIrrelevance_1970_ = lean_ctor_get_uint8(v___x_1963_, 6 as u32);
                        v_assignSyntheticOpaque_1971_ = lean_ctor_get_uint8(v___x_1963_, 7 as u32);
                        v_offsetCnstrs_1972_ = lean_ctor_get_uint8(v___x_1963_, 8 as u32);
                        v_etaStruct_1973_ = lean_ctor_get_uint8(v___x_1963_, 10 as u32);
                        v_univApprox_1974_ = lean_ctor_get_uint8(v___x_1963_, 11 as u32);
                        v_iota_1975_ = lean_ctor_get_uint8(v___x_1963_, 12 as u32);
                        v_beta_1976_ = lean_ctor_get_uint8(v___x_1963_, 13 as u32);
                        v_proj_1977_ = lean_ctor_get_uint8(v___x_1963_, 14 as u32);
                        v_zeta_1978_ = lean_ctor_get_uint8(v___x_1963_, 15 as u32);
                        v_zetaDelta_1979_ = lean_ctor_get_uint8(v___x_1963_, 16 as u32);
                        v_zetaUnused_1980_ = lean_ctor_get_uint8(v___x_1963_, 17 as u32);
                        v_zetaHave_1981_ = lean_ctor_get_uint8(v___x_1963_, 18 as u32);
                        v_isSharedCheck_2017_ = (!lean_is_exclusive(v___x_1963_)) as u8;
                        if v_isSharedCheck_2017_ == 0 {
                            v___x_1983_ = v___x_1963_;
                            v_isShared_1984_ = v_isSharedCheck_2017_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_1963_);
                            v___x_1983_ = lean_box(0);
                            v_isShared_1984_ = v_isSharedCheck_2017_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2018_ = lean_ctor_get(v___x_1961_, 0);
                        v_isSharedCheck_2025_ = (!lean_is_exclusive(v___x_1961_)) as u8;
                        if v_isSharedCheck_2025_ == 0 {
                            v___x_2020_ = v___x_1961_;
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2018_);
                            lean_dec(v___x_1961_);
                            v___x_2020_ = lean_box(0);
                            v_isShared_2021_ = v_isSharedCheck_2025_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_h_1939_);
                    v_a_2026_ = lean_ctor_get(v___x_1955_, 0);
                    v_isSharedCheck_2033_ = (!lean_is_exclusive(v___x_1955_)) as u8;
                    if v_isSharedCheck_2033_ == 0 {
                        v___x_2028_ = v___x_1955_;
                        v_isShared_2029_ = v_isSharedCheck_2033_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2026_);
                        lean_dec(v___x_1955_);
                        v___x_2028_ = lean_box(0);
                        v_isShared_2029_ = v_isSharedCheck_2033_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1951_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1951_, 0, v_a_1950_);
                v___x_1952_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_1952_, 0, v___x_1948_);
                lean_ctor_set(v___x_1952_, 1, v___x_1951_);
                lean_ctor_set_uint8(
                    v___x_1952_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_1937_,
                );
                v___x_1953_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1953_, 0, v___x_1952_);
                v___x_1954_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                return v___x_1954_;
            }
            2 => {
                v_trackZetaDelta_1985_ = lean_ctor_get_uint8(
                    v___y_1943_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1986_ = lean_ctor_get(v___y_1943_, 1);
                v_lctx_1987_ = lean_ctor_get(v___y_1943_, 2);
                v_localInstances_1988_ = lean_ctor_get(v___y_1943_, 3);
                v_defEqCtx_x3f_1989_ = lean_ctor_get(v___y_1943_, 4);
                v_synthPendingDepth_1990_ = lean_ctor_get(v___y_1943_, 5);
                v_canUnfold_x3f_1991_ = lean_ctor_get(v___y_1943_, 6);
                v_univApprox_1992_ = lean_ctor_get_uint8(
                    v___y_1943_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1993_ = lean_ctor_get_uint8(
                    v___y_1943_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1994_ = lean_ctor_get_uint8(
                    v___y_1943_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_1995_ = 1;
                if v_isShared_1984_ == 0 {
                    v_config_1997_ = v___x_1983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 0 as u32, v_foApprox_1964_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 1 as u32, v_ctxApprox_1965_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        2 as u32,
                        v_quasiPatternApprox_1966_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 3 as u32, v_constApprox_1967_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 4 as u32, v_isDefEqStuckEx_1968_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 5 as u32, v_unificationHints_1969_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 6 as u32, v_proofIrrelevance_1970_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2016_,
                        7 as u32,
                        v_assignSyntheticOpaque_1971_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 8 as u32, v_offsetCnstrs_1972_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 10 as u32, v_etaStruct_1973_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 11 as u32, v_univApprox_1974_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 12 as u32, v_iota_1975_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 13 as u32, v_beta_1976_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 14 as u32, v_proj_1977_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 15 as u32, v_zeta_1978_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 16 as u32, v_zetaDelta_1979_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 17 as u32, v_zetaUnused_1980_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2016_, 18 as u32, v_zetaHave_1981_);
                    v_config_1997_ = v_reuseFailAlloc_2016_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_1997_, 9 as u32, v___x_1995_);
                v___x_1998_ = l_Lean_Meta_Context_configKey(v___y_1943_);
                v___x_1999_ = lean_uint64_shift_right(v___x_1998_, v___x_1938_);
                v___x_2000_ = lean_uint64_shift_left(v___x_1999_, v___x_1938_);
                v___x_2001_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(l_reduceCtorEq___lam__2___closed__3),
                    core::ptr::addr_of_mut!(l_reduceCtorEq___lam__2___closed__3_once),
                    _init_l_reduceCtorEq___lam__2___closed__3,
                );
                v_key_2002_ = lean_uint64_lor(v___x_2000_, v___x_2001_);
                v___x_2003_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_2003_, 0, v_config_1997_);
                lean_ctor_set_uint64(
                    v___x_2003_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_2002_,
                );
                lean_inc(v_canUnfold_x3f_1991_);
                lean_inc(v_synthPendingDepth_1990_);
                lean_inc(v_defEqCtx_x3f_1989_);
                lean_inc_ref(v_localInstances_1988_);
                lean_inc_ref(v_lctx_1987_);
                lean_inc(v_zetaDeltaSet_1986_);
                v___x_2004_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_2004_, 0, v___x_2003_);
                lean_ctor_set(v___x_2004_, 1, v_zetaDeltaSet_1986_);
                lean_ctor_set(v___x_2004_, 2, v_lctx_1987_);
                lean_ctor_set(v___x_2004_, 3, v_localInstances_1988_);
                lean_ctor_set(v___x_2004_, 4, v_defEqCtx_x3f_1989_);
                lean_ctor_set(v___x_2004_, 5, v_synthPendingDepth_1990_);
                lean_ctor_set(v___x_2004_, 6, v_canUnfold_x3f_1991_);
                lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1985_,
                );
                lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1992_,
                );
                lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1993_,
                );
                lean_ctor_set_uint8(
                    v___x_2004_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1994_,
                );
                v___x_2005_ = l_Lean_Meta_mkEqFalse_x27(
                    v_a_1962_,
                    v___x_2004_,
                    v___y_1944_,
                    v___y_1945_,
                    v___y_1946_,
                );
                lean_dec_ref_known(v___x_2004_, 7);
                if lean_obj_tag(v___x_2005_) == 0 {
                    v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
                    lean_inc(v_a_2006_);
                    lean_dec_ref_known(v___x_2005_, 1);
                    v_a_1950_ = v_a_2006_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v___x_2005_) == 0 {
                        v_a_2007_ = lean_ctor_get(v___x_2005_, 0);
                        lean_inc(v_a_2007_);
                        lean_dec_ref_known(v___x_2005_, 1);
                        v_a_1950_ = v_a_2007_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2008_ = lean_ctor_get(v___x_2005_, 0);
                        v_isSharedCheck_2015_ = (!lean_is_exclusive(v___x_2005_)) as u8;
                        if v_isSharedCheck_2015_ == 0 {
                            v___x_2010_ = v___x_2005_;
                            v_isShared_2011_ = v_isSharedCheck_2015_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2008_);
                            lean_dec(v___x_2005_);
                            v___x_2010_ = lean_box(0);
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
                    v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
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
                    v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
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
                    v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
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
    mut v___x_2034_: *mut LeanObject,
    mut v___x_2035_: *mut LeanObject,
    mut v___x_2036_: *mut LeanObject,
    mut v_h_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
    mut v___y_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_26663__boxed_2046_: u8 = 0;
    let mut v___x_26664__boxed_2047_: u8 = 0;
    let mut v___x_26665__boxed_2048_: u64 = 0;
    let mut v_res_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_26663__boxed_2046_ = (lean_unbox(v___x_2034_) as u8);
    v___x_26664__boxed_2047_ = (lean_unbox(v___x_2035_) as u8);
    v___x_26665__boxed_2048_ = lean_unbox_uint64(v___x_2036_);
    lean_dec_ref(v___x_2036_);
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
    lean_dec(v___y_2044_);
    lean_dec_ref(v___y_2043_);
    lean_dec(v___y_2042_);
    lean_dec_ref(v___y_2041_);
    lean_dec(v___y_2040_);
    lean_dec_ref(v___y_2039_);
    lean_dec(v___y_2038_);
    return v_res_2049_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(
    mut v_k_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v_b_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2058_);
    lean_inc_ref(v___y_2057_);
    lean_inc(v___y_2056_);
    lean_inc_ref(v___y_2055_);
    lean_inc(v___y_2053_);
    lean_inc_ref(v___y_2052_);
    lean_inc(v___y_2051_);
    v___x_2060_ = lean_apply_9(
        v_k_2050_,
        v_b_2054_,
        v___y_2051_,
        v___y_2052_,
        v___y_2053_,
        v___y_2055_,
        v___y_2056_,
        v___y_2057_,
        v___y_2058_,
        lean_box(0),
    );
    return v___x_2060_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
    mut v___y_2063_: *mut LeanObject,
    mut v___y_2064_: *mut LeanObject,
    mut v_b_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2071_: *mut LeanObject = core::ptr::null_mut();
    v_res_2071_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v_b_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
    lean_dec(v___y_2069_);
    lean_dec_ref(v___y_2068_);
    lean_dec(v___y_2067_);
    lean_dec_ref(v___y_2066_);
    lean_dec(v___y_2064_);
    lean_dec_ref(v___y_2063_);
    lean_dec(v___y_2062_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(
    mut v_name_2072_: *mut LeanObject,
    mut v_bi_2073_: u8,
    mut v_type_2074_: *mut LeanObject,
    mut v_k_2075_: *mut LeanObject,
    mut v_kind_2076_: u8,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
    mut v___y_2083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2079_);
                lean_inc_ref(v___y_2078_);
                lean_inc(v___y_2077_);
                v___f_2085_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                lean_closure_set(v___f_2085_, 0, v_k_2075_);
                lean_closure_set(v___f_2085_, 1, v___y_2077_);
                lean_closure_set(v___f_2085_, 2, v___y_2078_);
                lean_closure_set(v___f_2085_, 3, v___y_2079_);
                v___x_2086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_2086_) == 0 {
                    return v___x_2086_;
                } else {
                    v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
                    v_isSharedCheck_2094_ = (!lean_is_exclusive(v___x_2086_)) as u8;
                    if v_isSharedCheck_2094_ == 0 {
                        v___x_2089_ = v___x_2086_;
                        v_isShared_2090_ = v_isSharedCheck_2094_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2087_);
                        lean_dec(v___x_2086_);
                        v___x_2089_ = lean_box(0);
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
                    v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
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
    mut v_name_2095_: *mut LeanObject,
    mut v_bi_2096_: *mut LeanObject,
    mut v_type_2097_: *mut LeanObject,
    mut v_k_2098_: *mut LeanObject,
    mut v_kind_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2108_: u8 = 0;
    let mut v_kind_boxed_2109_: u8 = 0;
    let mut v_res_2110_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2108_ = (lean_unbox(v_bi_2096_) as u8);
    v_kind_boxed_2109_ = (lean_unbox(v_kind_2099_) as u8);
    v_res_2110_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_2095_, v_bi_boxed_2108_, v_type_2097_, v_k_2098_, v_kind_boxed_2109_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
    lean_dec(v___y_2106_);
    lean_dec_ref(v___y_2105_);
    lean_dec(v___y_2104_);
    lean_dec_ref(v___y_2103_);
    lean_dec(v___y_2102_);
    lean_dec_ref(v___y_2101_);
    lean_dec(v___y_2100_);
    return v_res_2110_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(
    mut v_name_2111_: *mut LeanObject,
    mut v_type_2112_: *mut LeanObject,
    mut v_k_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
    mut v___y_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: u8 = 0;
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    v___x_2122_ = 0;
    v___x_2123_ = 0;
    v___x_2124_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_2111_, v___x_2122_, v_type_2112_, v_k_2113_, v___x_2123_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
    return v___x_2124_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg___boxed(
    mut v_name_2125_: *mut LeanObject,
    mut v_type_2126_: *mut LeanObject,
    mut v_k_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
    mut v___y_2129_: *mut LeanObject,
    mut v___y_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2136_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2134_);
    lean_dec_ref(v___y_2133_);
    lean_dec(v___y_2132_);
    lean_dec_ref(v___y_2131_);
    lean_dec(v___y_2130_);
    lean_dec_ref(v___y_2129_);
    lean_dec(v___y_2128_);
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
    mut v_e_2147_: *mut LeanObject,
    mut v_a_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2165_: u8 = 0;
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v_trackZetaDelta_2188_: u8 = 0;
    let mut v_zetaDeltaSet_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2195_: u8 = 0;
    let mut v_inTypeClassResolution_2196_: u8 = 0;
    let mut v_cacheInferType_2197_: u8 = 0;
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v_config_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u64 = 0;
    let mut v___x_2204_: u64 = 0;
    let mut v___x_2205_: u64 = 0;
    let mut v___x_2206_: u64 = 0;
    let mut v___x_2207_: u64 = 0;
    let mut v_key_2208_: u64 = 0;
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: u8 = 0;
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v_a_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2263_: u8 = 0;
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2267_: u8 = 0;
    let mut v_a_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2271_: u8 = 0;
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_reuseFailAlloc_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut v_isSharedCheck_2285_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2166_ = l_Lean_Meta_Context_config(v_a_2151_);
                v_foApprox_2167_ = lean_ctor_get_uint8(v___x_2166_, 0 as u32);
                v_ctxApprox_2168_ = lean_ctor_get_uint8(v___x_2166_, 1 as u32);
                v_quasiPatternApprox_2169_ = lean_ctor_get_uint8(v___x_2166_, 2 as u32);
                v_constApprox_2170_ = lean_ctor_get_uint8(v___x_2166_, 3 as u32);
                v_isDefEqStuckEx_2171_ = lean_ctor_get_uint8(v___x_2166_, 4 as u32);
                v_unificationHints_2172_ = lean_ctor_get_uint8(v___x_2166_, 5 as u32);
                v_proofIrrelevance_2173_ = lean_ctor_get_uint8(v___x_2166_, 6 as u32);
                v_assignSyntheticOpaque_2174_ = lean_ctor_get_uint8(v___x_2166_, 7 as u32);
                v_offsetCnstrs_2175_ = lean_ctor_get_uint8(v___x_2166_, 8 as u32);
                v_etaStruct_2176_ = lean_ctor_get_uint8(v___x_2166_, 10 as u32);
                v_univApprox_2177_ = lean_ctor_get_uint8(v___x_2166_, 11 as u32);
                v_iota_2178_ = lean_ctor_get_uint8(v___x_2166_, 12 as u32);
                v_beta_2179_ = lean_ctor_get_uint8(v___x_2166_, 13 as u32);
                v_proj_2180_ = lean_ctor_get_uint8(v___x_2166_, 14 as u32);
                v_zeta_2181_ = lean_ctor_get_uint8(v___x_2166_, 15 as u32);
                v_zetaDelta_2182_ = lean_ctor_get_uint8(v___x_2166_, 16 as u32);
                v_zetaUnused_2183_ = lean_ctor_get_uint8(v___x_2166_, 17 as u32);
                v_zetaHave_2184_ = lean_ctor_get_uint8(v___x_2166_, 18 as u32);
                v_isSharedCheck_2285_ = (!lean_is_exclusive(v___x_2166_)) as u8;
                if v_isSharedCheck_2285_ == 0 {
                    v___x_2186_ = v___x_2166_;
                    v_isShared_2187_ = v_isSharedCheck_2285_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v___x_2166_);
                    v___x_2186_ = lean_box(0);
                    v_isShared_2187_ = v_isSharedCheck_2285_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_2157_) == 0 {
                    v_a_2158_ = lean_ctor_get(v___y_2157_, 0);
                    v_isSharedCheck_2165_ = (!lean_is_exclusive(v___y_2157_)) as u8;
                    if v_isSharedCheck_2165_ == 0 {
                        v___x_2160_ = v___y_2157_;
                        v_isShared_2161_ = v_isSharedCheck_2165_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2158_);
                        lean_dec(v___y_2157_);
                        v___x_2160_ = lean_box(0);
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
                    v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
                    v___x_2163_ = v_reuseFailAlloc_2164_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2163_;
            }
            4 => {
                v_trackZetaDelta_2188_ = lean_ctor_get_uint8(
                    v_a_2151_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2189_ = lean_ctor_get(v_a_2151_, 1);
                v_lctx_2190_ = lean_ctor_get(v_a_2151_, 2);
                v_localInstances_2191_ = lean_ctor_get(v_a_2151_, 3);
                v_defEqCtx_x3f_2192_ = lean_ctor_get(v_a_2151_, 4);
                v_synthPendingDepth_2193_ = lean_ctor_get(v_a_2151_, 5);
                v_canUnfold_x3f_2194_ = lean_ctor_get(v_a_2151_, 6);
                v_univApprox_2195_ = lean_ctor_get_uint8(
                    v_a_2151_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2196_ = lean_ctor_get_uint8(
                    v_a_2151_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2197_ = lean_ctor_get_uint8(
                    v_a_2151_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                lean_inc_ref(v_e_2147_);
                v___x_2198_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2147_, v_a_2152_);
                if lean_obj_tag(v___x_2198_) == 0 {
                    v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
                    lean_inc(v_a_2199_);
                    lean_dec_ref_known(v___x_2198_, 1);
                    v___x_2200_ = 3;
                    if v_isShared_2187_ == 0 {
                        v_config_2202_ = v___x_2186_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 0, (19) as u32);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 0 as u32, v_foApprox_2167_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 1 as u32, v_ctxApprox_2168_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            2 as u32,
                            v_quasiPatternApprox_2169_,
                        );
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 3 as u32, v_constApprox_2170_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            4 as u32,
                            v_isDefEqStuckEx_2171_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            5 as u32,
                            v_unificationHints_2172_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            6 as u32,
                            v_proofIrrelevance_2173_,
                        );
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_2276_,
                            7 as u32,
                            v_assignSyntheticOpaque_2174_,
                        );
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 8 as u32, v_offsetCnstrs_2175_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 10 as u32, v_etaStruct_2176_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 11 as u32, v_univApprox_2177_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 12 as u32, v_iota_2178_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 13 as u32, v_beta_2179_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 14 as u32, v_proj_2180_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 15 as u32, v_zeta_2181_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 16 as u32, v_zetaDelta_2182_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 17 as u32, v_zetaUnused_2183_);
                        lean_ctor_set_uint8(v_reuseFailAlloc_2276_, 18 as u32, v_zetaHave_2184_);
                        v_config_2202_ = v_reuseFailAlloc_2276_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2186_);
                    lean_dec_ref(v_e_2147_);
                    v_a_2277_ = lean_ctor_get(v___x_2198_, 0);
                    v_isSharedCheck_2284_ = (!lean_is_exclusive(v___x_2198_)) as u8;
                    if v_isSharedCheck_2284_ == 0 {
                        v___x_2279_ = v___x_2198_;
                        v_isShared_2280_ = v_isSharedCheck_2284_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2277_);
                        lean_dec(v___x_2198_);
                        v___x_2279_ = lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2284_;
                        state = 13;
                        continue;
                    }
                }
            }
            5 => {
                lean_ctor_set_uint8(v_config_2202_, 9 as u32, v___x_2200_);
                v___x_2203_ = l_Lean_Meta_Context_configKey(v_a_2151_);
                v___x_2204_ = 3u64;
                v___x_2205_ = lean_uint64_shift_right(v___x_2203_, v___x_2204_);
                v___x_2206_ = lean_uint64_shift_left(v___x_2205_, v___x_2204_);
                v___x_2207_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(l_reduceCtorEq___closed__0),
                    core::ptr::addr_of_mut!(l_reduceCtorEq___closed__0_once),
                    _init_l_reduceCtorEq___closed__0,
                );
                v_key_2208_ = lean_uint64_lor(v___x_2206_, v___x_2207_);
                v___x_2209_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_2209_, 0, v_config_2202_);
                lean_ctor_set_uint64(
                    v___x_2209_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_2208_,
                );
                lean_inc(v_canUnfold_x3f_2194_);
                lean_inc(v_synthPendingDepth_2193_);
                lean_inc(v_defEqCtx_x3f_2192_);
                lean_inc_ref(v_localInstances_2191_);
                lean_inc_ref(v_lctx_2190_);
                lean_inc(v_zetaDeltaSet_2189_);
                v___x_2210_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_2210_, 0, v___x_2209_);
                lean_ctor_set(v___x_2210_, 1, v_zetaDeltaSet_2189_);
                lean_ctor_set(v___x_2210_, 2, v_lctx_2190_);
                lean_ctor_set(v___x_2210_, 3, v_localInstances_2191_);
                lean_ctor_set(v___x_2210_, 4, v_defEqCtx_x3f_2192_);
                lean_ctor_set(v___x_2210_, 5, v_synthPendingDepth_2193_);
                lean_ctor_set(v___x_2210_, 6, v_canUnfold_x3f_2194_);
                lean_ctor_set_uint8(
                    v___x_2210_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2188_,
                );
                lean_ctor_set_uint8(
                    v___x_2210_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2195_,
                );
                lean_ctor_set_uint8(
                    v___x_2210_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2196_,
                );
                lean_ctor_set_uint8(
                    v___x_2210_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2197_,
                );
                v___x_2211_ = l_Lean_Expr_cleanupAnnotations(v_a_2199_);
                v___x_2212_ = l_Lean_Expr_isApp(v___x_2211_);
                if v___x_2212_ == 0 {
                    lean_dec_ref(v___x_2211_);
                    lean_dec_ref(v_e_2147_);
                    v___x_2213_ = lean_box(0);
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
                    lean_dec_ref_known(v___x_2210_, 7);
                    v___y_2157_ = v___x_2214_;
                    state = 1;
                    continue;
                } else {
                    v_arg_2215_ = lean_ctor_get(v___x_2211_, 1);
                    lean_inc_ref(v_arg_2215_);
                    v___x_2216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2211_);
                    v___x_2217_ = l_Lean_Expr_isApp(v___x_2216_);
                    if v___x_2217_ == 0 {
                        lean_dec_ref(v___x_2216_);
                        lean_dec_ref(v_arg_2215_);
                        lean_dec_ref(v_e_2147_);
                        v___x_2218_ = lean_box(0);
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
                        lean_dec_ref_known(v___x_2210_, 7);
                        v___y_2157_ = v___x_2219_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_2220_ = lean_ctor_get(v___x_2216_, 1);
                        lean_inc_ref(v_arg_2220_);
                        v___x_2221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2216_);
                        v___x_2222_ = l_Lean_Expr_isApp(v___x_2221_);
                        if v___x_2222_ == 0 {
                            lean_dec_ref(v___x_2221_);
                            lean_dec_ref(v_arg_2220_);
                            lean_dec_ref(v_arg_2215_);
                            lean_dec_ref(v_e_2147_);
                            v___x_2223_ = lean_box(0);
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
                            lean_dec_ref_known(v___x_2210_, 7);
                            v___y_2157_ = v___x_2224_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2221_);
                            v___x_2226_ = l_reduceCtorEq___closed__2;
                            v___x_2227_ = l_Lean_Expr_isConstOf(v___x_2225_, v___x_2226_);
                            lean_dec_ref(v___x_2225_);
                            if v___x_2227_ == 0 {
                                lean_dec_ref(v_arg_2220_);
                                lean_dec_ref(v_arg_2215_);
                                lean_dec_ref(v_e_2147_);
                                v___x_2228_ = lean_box(0);
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
                                lean_dec_ref_known(v___x_2210_, 7);
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
                                if lean_obj_tag(v___x_2230_) == 0 {
                                    v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
                                    lean_inc(v_a_2231_);
                                    lean_dec_ref_known(v___x_2230_, 1);
                                    v___x_2232_ = l_Lean_Meta_constructorApp_x27_x3f(
                                        v_arg_2215_,
                                        v___x_2210_,
                                        v_a_2152_,
                                        v_a_2153_,
                                        v_a_2154_,
                                    );
                                    if lean_obj_tag(v___x_2232_) == 0 {
                                        v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
                                        v_isSharedCheck_2259_ =
                                            (!lean_is_exclusive(v___x_2232_)) as u8;
                                        if v_isSharedCheck_2259_ == 0 {
                                            v___x_2235_ = v___x_2232_;
                                            v_isShared_2236_ = v_isSharedCheck_2259_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2233_);
                                            lean_dec(v___x_2232_);
                                            v___x_2235_ = lean_box(0);
                                            v_isShared_2236_ = v_isSharedCheck_2259_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_2231_);
                                        lean_dec_ref_known(v___x_2210_, 7);
                                        lean_dec_ref(v_e_2147_);
                                        v_a_2260_ = lean_ctor_get(v___x_2232_, 0);
                                        v_isSharedCheck_2267_ =
                                            (!lean_is_exclusive(v___x_2232_)) as u8;
                                        if v_isSharedCheck_2267_ == 0 {
                                            v___x_2262_ = v___x_2232_;
                                            v_isShared_2263_ = v_isSharedCheck_2267_;
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2260_);
                                            lean_dec(v___x_2232_);
                                            v___x_2262_ = lean_box(0);
                                            v_isShared_2263_ = v_isSharedCheck_2267_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_arg_2215_);
                                    lean_dec_ref_known(v___x_2210_, 7);
                                    lean_dec_ref(v_e_2147_);
                                    v_a_2268_ = lean_ctor_get(v___x_2230_, 0);
                                    v_isSharedCheck_2275_ = (!lean_is_exclusive(v___x_2230_)) as u8;
                                    if v_isSharedCheck_2275_ == 0 {
                                        v___x_2270_ = v___x_2230_;
                                        v_isShared_2271_ = v_isSharedCheck_2275_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2268_);
                                        lean_dec(v___x_2230_);
                                        v___x_2270_ = lean_box(0);
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
                if lean_obj_tag(v_a_2231_) == 1 {
                    if lean_obj_tag(v_a_2233_) == 1 {
                        v_val_2242_ = lean_ctor_get(v_a_2231_, 0);
                        lean_inc(v_val_2242_);
                        lean_dec_ref_known(v_a_2231_, 1);
                        v_val_2243_ = lean_ctor_get(v_a_2233_, 0);
                        lean_inc(v_val_2243_);
                        lean_dec_ref_known(v_a_2233_, 1);
                        v_fst_2244_ = lean_ctor_get(v_val_2242_, 0);
                        lean_inc(v_fst_2244_);
                        lean_dec(v_val_2242_);
                        v_toConstantVal_2245_ = lean_ctor_get(v_fst_2244_, 0);
                        lean_inc_ref(v_toConstantVal_2245_);
                        lean_dec(v_fst_2244_);
                        v_fst_2246_ = lean_ctor_get(v_val_2243_, 0);
                        lean_inc(v_fst_2246_);
                        lean_dec(v_val_2243_);
                        v_toConstantVal_2247_ = lean_ctor_get(v_fst_2246_, 0);
                        lean_inc_ref(v_toConstantVal_2247_);
                        lean_dec(v_fst_2246_);
                        v_name_2248_ = lean_ctor_get(v_toConstantVal_2245_, 0);
                        lean_inc(v_name_2248_);
                        lean_dec_ref(v_toConstantVal_2245_);
                        v_name_2249_ = lean_ctor_get(v_toConstantVal_2247_, 0);
                        lean_inc(v_name_2249_);
                        lean_dec_ref(v_toConstantVal_2247_);
                        v___x_2250_ = lean_name_eq(v_name_2248_, v_name_2249_);
                        lean_dec(v_name_2249_);
                        lean_dec(v_name_2248_);
                        if v___x_2250_ == 0 {
                            if v___x_2227_ == 0 {
                                lean_dec_ref_known(v___x_2210_, 7);
                                lean_dec_ref(v_e_2147_);
                                state = 7;
                                continue;
                            } else {
                                lean_del_object(v___x_2235_);
                                v___x_2251_ = lean_box((v___x_2250_) as usize);
                                v___x_2252_ = lean_box((v___x_2227_) as usize);
                                v___x_2253_ = l_reduceCtorEq___boxed__const__1;
                                v___f_2254_ = lean_alloc_closure(
                                    l_reduceCtorEq___lam__2___boxed as *mut core::ffi::c_void,
                                    12,
                                    3,
                                );
                                lean_closure_set(v___f_2254_, 0, v___x_2251_);
                                lean_closure_set(v___f_2254_, 1, v___x_2252_);
                                lean_closure_set(v___f_2254_, 2, v___x_2253_);
                                v___x_2255_ = l_reduceCtorEq___closed__4;
                                v___x_2256_ = l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0___redArg(v___x_2255_, v_e_2147_, v___f_2254_, v_a_2148_, v_a_2149_, v_a_2150_, v___x_2210_, v_a_2152_, v_a_2153_, v_a_2154_);
                                lean_dec_ref_known(v___x_2210_, 7);
                                v___y_2157_ = v___x_2256_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v___x_2210_, 7);
                            lean_dec_ref(v_e_2147_);
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2235_);
                        lean_dec_ref(v_e_2147_);
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
                        lean_dec_ref_known(v___x_2210_, 7);
                        lean_dec(v_a_2233_);
                        lean_dec_ref_known(v_a_2231_, 1);
                        v___y_2157_ = v___x_2257_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2235_);
                    lean_dec_ref(v_e_2147_);
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
                    lean_dec_ref_known(v___x_2210_, 7);
                    lean_dec(v_a_2233_);
                    lean_dec(v_a_2231_);
                    v___y_2157_ = v___x_2258_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_2238_ = l_reduceIte___closed__0;
                if v_isShared_2236_ == 0 {
                    lean_ctor_set(v___x_2235_, 0, v___x_2238_);
                    v___x_2240_ = v___x_2235_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
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
                    v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
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
                    v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
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
                    v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
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
    mut v_e_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
    mut v_a_2289_: *mut LeanObject,
    mut v_a_2290_: *mut LeanObject,
    mut v_a_2291_: *mut LeanObject,
    mut v_a_2292_: *mut LeanObject,
    mut v_a_2293_: *mut LeanObject,
    mut v_a_2294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2295_: *mut LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_reduceCtorEq(
        v_e_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_,
    );
    lean_dec(v_a_2293_);
    lean_dec_ref(v_a_2292_);
    lean_dec(v_a_2291_);
    lean_dec_ref(v_a_2290_);
    lean_dec(v_a_2289_);
    lean_dec_ref(v_a_2288_);
    lean_dec(v_a_2287_);
    return v_res_2295_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(
    mut v_00_u03b1_2296_: *mut LeanObject,
    mut v_name_2297_: *mut LeanObject,
    mut v_bi_2298_: u8,
    mut v_type_2299_: *mut LeanObject,
    mut v_k_2300_: *mut LeanObject,
    mut v_kind_2301_: u8,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
    mut v___y_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
    mut v___y_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    v___x_2310_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___redArg(v_name_2297_, v_bi_2298_, v_type_2299_, v_k_2300_, v_kind_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
    return v___x_2310_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0___boxed(
    mut v_00_u03b1_2311_: *mut LeanObject,
    mut v_name_2312_: *mut LeanObject,
    mut v_bi_2313_: *mut LeanObject,
    mut v_type_2314_: *mut LeanObject,
    mut v_k_2315_: *mut LeanObject,
    mut v_kind_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
    mut v___y_2319_: *mut LeanObject,
    mut v___y_2320_: *mut LeanObject,
    mut v___y_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2325_: u8 = 0;
    let mut v_kind_boxed_2326_: u8 = 0;
    let mut v_res_2327_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2325_ = (lean_unbox(v_bi_2313_) as u8);
    v_kind_boxed_2326_ = (lean_unbox(v_kind_2316_) as u8);
    v_res_2327_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0_spec__0(v_00_u03b1_2311_, v_name_2312_, v_bi_boxed_2325_, v_type_2314_, v_k_2315_, v_kind_boxed_2326_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
    lean_dec(v___y_2323_);
    lean_dec_ref(v___y_2322_);
    lean_dec(v___y_2321_);
    lean_dec_ref(v___y_2320_);
    lean_dec(v___y_2319_);
    lean_dec_ref(v___y_2318_);
    lean_dec(v___y_2317_);
    return v_res_2327_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00reduceCtorEq_spec__0(
    mut v_00_u03b1_2328_: *mut LeanObject,
    mut v_name_2329_: *mut LeanObject,
    mut v_type_2330_: *mut LeanObject,
    mut v_k_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
    mut v___y_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2341_: *mut LeanObject,
    mut v_name_2342_: *mut LeanObject,
    mut v_type_2343_: *mut LeanObject,
    mut v_k_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
    mut v___y_2349_: *mut LeanObject,
    mut v___y_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2351_);
    lean_dec_ref(v___y_2350_);
    lean_dec(v___y_2349_);
    lean_dec_ref(v___y_2348_);
    lean_dec(v___y_2347_);
    lean_dec_ref(v___y_2346_);
    lean_dec(v___y_2345_);
    return v_res_2353_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_()
-> *mut LeanObject {
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    v___x_2369_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
    v___x_2370_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
    v___x_2371_ = lean_alloc_closure(l_reduceCtorEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_2372_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2369_, v___x_2370_, v___x_2371_);
    return v___x_2372_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16____boxed(
    mut v_a_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2374_: *mut LeanObject = core::ptr::null_mut();
    v_res_2374_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
    return v_res_2374_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_()
-> *mut LeanObject {
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    v___x_2375_ = lean_alloc_closure(l_reduceCtorEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_2376_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2376_, 0, v___x_2375_);
    return v___x_2376_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_()
-> *mut LeanObject {
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    v___x_2378_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
    v___x_2379_ = 1;
    v___x_2380_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
    v___x_2381_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2378_, v___x_2379_, v___x_2380_);
    return v___x_2381_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18____boxed(
    mut v_a_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2383_: *mut LeanObject = core::ptr::null_mut();
    v_res_2383_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
    return v_res_2383_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: u8 = 0;
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    v___x_2385_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_;
    v___x_2386_ = 1;
    v___x_2387_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_);
    v___x_2388_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2385_, v___x_2386_, v___x_2387_);
    return v___x_2388_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20____boxed(
    mut v_a_2389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2390_: *mut LeanObject = core::ptr::null_mut();
    v_res_2390_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
    return v_res_2390_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceIte_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_15_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_17_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceIte___regBuiltin_reduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3249294384____hygCtx___hyg_19_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceDIte_declare__10_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_15_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_17_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceDIte___regBuiltin_reduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_3647891266____hygCtx___hyg_19_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceIte_declare__15_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_15_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_17_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceIte___regBuiltin_dreduceIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_352607467____hygCtx___hyg_19_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_dreduceDIte_declare__20_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_15_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_17_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__dreduceDIte___regBuiltin_dreduceDIte_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1959124870____hygCtx___hyg_19_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0____regBuiltin_reduceCtorEq_declare__25_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_16_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_18_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_0__reduceCtorEq___regBuiltin_reduceCtorEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core_1976305802____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorRecognizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
}
