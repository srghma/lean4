// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.String
// Imports: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char Lean.Meta.StringLitProof
use crate::r#gen::Init::Data::String::Basic::l_String_decLE;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_isAppOfArity, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkRawNatLit, l_Lean_mkStrLit,
};
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getCharValue_x3f, l_Lean_Meta_getStringValue_x3f,
};
use crate::r#gen::Lean::Meta::StringLitProof::{
    initialize_Lean_Meta_StringLitProof, l_Lean_Meta_mkStringLitNeProof,
    runtime_initialize_Lean_Meta_StringLitProof,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Char::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Util::{
    l_Lean_Meta_Simp_evalEqPropStep, l_Lean_Meta_Simp_evalNePropStep,
    l_Lean_Meta_Simp_evalPropStep___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    l_Lean_Meta_Simp_addSEvalprocBuiltinAttr, l_Lean_Meta_Simp_addSimprocBuiltinAttr,
    l_Lean_Meta_Simp_registerBuiltinDSimproc, l_Lean_Meta_Simp_registerBuiltinSimproc,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{lean_string_data, lean_string_dec_lt};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_string_dec_eq, lean_uint32_to_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_String_reduceAppend___redArg___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [72, 65, 112, 112, 101, 110, 100, 0],
    };
static mut l_String_reduceAppend___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceAppend___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceAppend___redArg___closed__1_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [104, 65, 112, 112, 101, 110, 100, 0],
    };
static mut l_String_reduceAppend___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceAppend___redArg___closed__1_value) as *mut LeanObject;
static l_String_reduceAppend___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceAppend___redArg___closed__0_value) as *mut LeanObject,
        2304392498378253193 as *mut LeanObject,
    ],
};
pub static l_String_reduceAppend___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceAppend___redArg___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceAppend___redArg___closed__1_value) as *mut LeanObject,
        16790970975024013749 as *mut LeanObject,
    ],
};
static mut l_String_reduceAppend___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceAppend___redArg___closed__2_value) as *mut LeanObject;
pub static l_String_reduceAppend___redArg___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
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
static mut l_String_reduceAppend___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceAppend___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 101, 100, 117, 99, 101, 65, 112, 112, 101, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,9584051508531737474 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceAppend___redArg___closed__2_value) as *mut LeanObject,((( 6 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value: LeanArrayObject<7> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*7) as u16, other: 0, tag: 246 }, m_size: 7, m_capacity: 7, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 105, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__1_value) as *mut LeanObject,18135193680607614554 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__0_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__3_value) as *mut LeanObject,8614124190858717794 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4_value) as *mut LeanObject;
pub static l_String_reduceOfList___redArg___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [111, 102, 76, 105, 115, 116, 0],
    };
static mut l_String_reduceOfList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceOfList___redArg___closed__0_value) as *mut LeanObject;
static l_String_reduceOfList___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l_String_reduceOfList___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceOfList___redArg___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceOfList___redArg___closed__0_value) as *mut LeanObject,
        16845443598000453238 as *mut LeanObject,
    ],
};
static mut l_String_reduceOfList___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceOfList___redArg___closed__1_value) as *mut LeanObject;
pub static l_String_reduceOfList___redArg___closed__2_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_String_reduceOfList___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceOfList___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 101, 100, 117, 99, 101, 79, 102, 76, 105, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value) as *mut LeanObject,18000182496940561748 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceOfList___redArg___closed__1_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value: LeanArrayObject<2> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 104, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__1_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0_value) as *mut LeanObject,14164462494711235346 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__1_value) as *mut LeanObject,18098914779984442139 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceToList___redArg___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [116, 111, 76, 105, 115, 116, 0],
    };
static mut l_String_reduceToList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceToList___redArg___closed__0_value) as *mut LeanObject;
static l_String_reduceToList___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l_String_reduceToList___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceToList___redArg___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceToList___redArg___closed__0_value) as *mut LeanObject,
        11662297882638581575 as *mut LeanObject,
    ],
};
static mut l_String_reduceToList___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceToList___redArg___closed__1_value) as *mut LeanObject;
pub static l_String_reduceToList___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__0_value) as *mut LeanObject,14164462494711235346 as *mut LeanObject] };
static mut l_String_reduceToList___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceToList___redArg___closed__2_value) as *mut LeanObject;
static mut l_String_reduceToList___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_reduceToList___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceToList___redArg___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_String_reduceToList___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceToList___redArg___closed__4_value) as *mut LeanObject;
static mut l_String_reduceToList___redArg___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_reduceToList___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_String_reduceToList___redArg___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_reduceToList___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_String_reduceToList___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_reduceToList___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_String_reduceToList___redArg___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_reduceToList___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 101, 100, 117, 99, 101, 84, 111, 76, 105, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value) as *mut LeanObject,223486073758669100 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceToList___redArg___closed__1_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value: LeanArrayObject<2> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reducePush___redArg___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [112, 117, 115, 104, 0],
};
static mut l_String_reducePush___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reducePush___redArg___closed__0_value) as *mut LeanObject;
static l_String_reducePush___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l_String_reducePush___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reducePush___redArg___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_String_reducePush___redArg___closed__0_value) as *mut LeanObject,
        4793256897768380139 as *mut LeanObject,
    ],
};
static mut l_String_reducePush___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reducePush___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 100, 117, 99, 101, 80, 117, 115, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value) as *mut LeanObject,2082292272647316297 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reducePush___redArg___closed__1_value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value: LeanArrayObject<3> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceSingleton___redArg___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [115, 105, 110, 103, 108, 101, 116, 111, 110, 0],
    };
static mut l_String_reduceSingleton___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceSingleton___redArg___closed__0_value) as *mut LeanObject;
static l_String_reduceSingleton___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l_String_reduceSingleton___redArg___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_String_reduceSingleton___redArg___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_String_reduceSingleton___redArg___closed__0_value)
                as *mut LeanObject,
            15777313802428938545 as *mut LeanObject,
        ],
    };
static mut l_String_reduceSingleton___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceSingleton___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [114, 101, 100, 117, 99, 101, 83, 105, 110, 103, 108, 101, 116, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value) as *mut LeanObject,8719129924854569217 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceSingleton___redArg___closed__1_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value: LeanArrayObject<2> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_: *mut LeanObject = core::ptr::null_mut();
static mut l_String_reduceToSingleton___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_reduceToSingleton___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 117, 99, 101, 84, 111, 83, 105, 110, 103, 108, 101, 116, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value) as *mut LeanObject,10111087938522935996 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value: LeanArrayObject<1> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12__value) as *mut LeanObject;
pub static l_String_reduceBinPred___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
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
static mut l_String_reduceBinPred___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBinPred___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceBoolPred___redArg___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_String_reduceBoolPred___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceBoolPred___redArg___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_String_reduceBoolPred___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__1_value) as *mut LeanObject;
static l_String_reduceBoolPred___redArg___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__0_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_String_reduceBoolPred___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__1_value) as *mut LeanObject,
        15761733860085307253 as *mut LeanObject,
    ],
};
static mut l_String_reduceBoolPred___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__2_value) as *mut LeanObject;
static mut l_String_reduceBoolPred___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_reduceBoolPred___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceBoolPred___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_String_reduceBoolPred___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__4_value) as *mut LeanObject;
static l_String_reduceBoolPred___redArg___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__0_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_String_reduceBoolPred___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__5_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__4_value) as *mut LeanObject,
        9255189395584251158 as *mut LeanObject,
    ],
};
static mut l_String_reduceBoolPred___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBoolPred___redArg___closed__5_value) as *mut LeanObject;
static mut l_String_reduceBoolPred___redArg___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_reduceBoolPred___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceLT___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceLT___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceLT___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceLT___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceLT___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceLT___redArg___closed__1_value) as *mut LeanObject;
static l_String_reduceLT___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceLT___redArg___closed__0_value) as *mut LeanObject,
        17878876274162330439 as *mut LeanObject,
    ],
};
pub static l_String_reduceLT___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceLT___redArg___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceLT___redArg___closed__1_value) as *mut LeanObject,
        11833570877100518198 as *mut LeanObject,
    ],
};
static mut l_String_reduceLT___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceLT___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value) as *mut LeanObject,7193177899468030291 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceLT___redArg___closed__2_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value: LeanArrayObject<5> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceLE___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceLE___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceLE___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceLE___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceLE___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceLE___redArg___closed__1_value) as *mut LeanObject;
static l_String_reduceLE___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceLE___redArg___closed__0_value) as *mut LeanObject,
        8347582161988589016 as *mut LeanObject,
    ],
};
pub static l_String_reduceLE___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceLE___redArg___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceLE___redArg___closed__1_value) as *mut LeanObject,
        7316284823769321069 as *mut LeanObject,
    ],
};
static mut l_String_reduceLE___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceLE___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value) as *mut LeanObject,13333795251982996661 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceLE___redArg___closed__2_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value: LeanArrayObject<5> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceGT___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceGT___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceGT___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceGT___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceGT___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceGT___redArg___closed__1_value) as *mut LeanObject;
static l_String_reduceGT___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceGT___redArg___closed__0_value) as *mut LeanObject,
        2272833755566510320 as *mut LeanObject,
    ],
};
pub static l_String_reduceGT___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceGT___redArg___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceGT___redArg___closed__1_value) as *mut LeanObject,
        9426339939459091439 as *mut LeanObject,
    ],
};
static mut l_String_reduceGT___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceGT___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 71, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value) as *mut LeanObject,5920291787773037861 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceGE___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceGE___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceGE___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceGE___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceGE___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceGE___redArg___closed__1_value) as *mut LeanObject;
static l_String_reduceGE___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceGE___redArg___closed__0_value) as *mut LeanObject,
        1755019837031360842 as *mut LeanObject,
    ],
};
pub static l_String_reduceGE___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceGE___redArg___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceGE___redArg___closed__1_value) as *mut LeanObject,
        5555145617058846791 as *mut LeanObject,
    ],
};
static mut l_String_reduceGE___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceGE___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 71, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value) as *mut LeanObject,8000299302077408192 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceEq___closed__0_value: LeanStringObject<3> = LeanStringObject {
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
static mut l_String_reduceEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceEq___closed__0_value) as *mut LeanObject;
pub static l_String_reduceEq___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceEq___closed__0_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_String_reduceEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceEq___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value) as *mut LeanObject,12386435122314162914 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceEq___closed__1_value) as *mut LeanObject,((( 3 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value: LeanArrayObject<4> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceNe___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceNe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceNe___closed__0_value) as *mut LeanObject;
pub static l_String_reduceNe___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceNe___closed__0_value) as *mut LeanObject,
        6695605208187598753 as *mut LeanObject,
    ],
};
static mut l_String_reduceNe___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceNe___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 100, 117, 99, 101, 78, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject,5578944351063537809 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject,16612019923665488825 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value: LeanArrayObject<5> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__4_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceBEq___redArg___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceBEq___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBEq___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceBEq___redArg___closed__1_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceBEq___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBEq___redArg___closed__1_value) as *mut LeanObject;
static l_String_reduceBEq___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceBEq___redArg___closed__0_value) as *mut LeanObject,
        16093780639914376387 as *mut LeanObject,
    ],
};
pub static l_String_reduceBEq___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_reduceBEq___redArg___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_String_reduceBEq___redArg___closed__1_value) as *mut LeanObject,
        9753356465987597394 as *mut LeanObject,
    ],
};
static mut l_String_reduceBEq___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBEq___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value) as *mut LeanObject,9008129793804705870 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceBEq___redArg___closed__2_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value: LeanArrayObject<5> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_: *mut LeanObject = core::ptr::null_mut();
pub static l_String_reduceBNe___redArg___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_reduceBNe___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBNe___redArg___closed__0_value) as *mut LeanObject;
pub static l_String_reduceBNe___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_String_reduceBNe___redArg___closed__0_value) as *mut LeanObject,
        943799886658452456 as *mut LeanObject,
    ],
};
static mut l_String_reduceBNe___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_reduceBNe___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 101, 66, 78, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,3136308715950998022 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value) as *mut LeanObject,5376045812162746608 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_String_reduceBNe___redArg___closed__1_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value: LeanArrayObject<5> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_String_fromExpr_x3f___redArg(mut v_e_1875_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    v___x_1877_ = l_Lean_Meta_getStringValue_x3f(v_e_1875_);
    v___x_1878_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1878_, 0, v___x_1877_);
    return v___x_1878_;
}
pub unsafe fn l_String_fromExpr_x3f___redArg___boxed(
    mut v_e_1879_: *mut LeanObject,
    mut v_a_1880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1881_: *mut LeanObject = core::ptr::null_mut();
    v_res_1881_ = l_String_fromExpr_x3f___redArg(v_e_1879_);
    return v_res_1881_;
}
pub unsafe fn l_String_fromExpr_x3f(
    mut v_e_1882_: *mut LeanObject,
    mut v_a_1883_: *mut LeanObject,
    mut v_a_1884_: *mut LeanObject,
    mut v_a_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
    mut v_a_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_String_fromExpr_x3f___redArg(v_e_1882_);
    return v___x_1891_;
}
pub unsafe fn l_String_fromExpr_x3f___boxed(
    mut v_e_1892_: *mut LeanObject,
    mut v_a_1893_: *mut LeanObject,
    mut v_a_1894_: *mut LeanObject,
    mut v_a_1895_: *mut LeanObject,
    mut v_a_1896_: *mut LeanObject,
    mut v_a_1897_: *mut LeanObject,
    mut v_a_1898_: *mut LeanObject,
    mut v_a_1899_: *mut LeanObject,
    mut v_a_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1901_: *mut LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_String_fromExpr_x3f(
        v_e_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_,
    );
    lean_dec(v_a_1899_);
    lean_dec_ref(v_a_1898_);
    lean_dec(v_a_1897_);
    lean_dec_ref(v_a_1896_);
    lean_dec(v_a_1895_);
    lean_dec_ref(v_a_1894_);
    lean_dec(v_a_1893_);
    return v_res_1901_;
}
pub unsafe fn l_String_reduceAppend___redArg(mut v_e_1909_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: u8 = 0;
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v_val_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1929_: u8 = 0;
    let mut v_val_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1942_: u8 = 0;
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1947_: u8 = 0;
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1911_ = l_String_reduceAppend___redArg___closed__2;
                v___x_1912_ = lean_unsigned_to_nat(6);
                v___x_1913_ = l_Lean_Expr_isAppOfArity(v_e_1909_, v___x_1911_, v___x_1912_);
                if v___x_1913_ == 0 {
                    v___x_1914_ = l_String_reduceAppend___redArg___closed__3;
                    v___x_1915_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1915_, 0, v___x_1914_);
                    return v___x_1915_;
                } else {
                    v___x_1916_ = l_Lean_Expr_appFn_x21(v_e_1909_);
                    v___x_1917_ = l_Lean_Expr_appArg_x21(v___x_1916_);
                    lean_dec_ref(v___x_1916_);
                    v___x_1918_ = l_String_fromExpr_x3f___redArg(v___x_1917_);
                    v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
                    v_isSharedCheck_1952_ = (!lean_is_exclusive(v___x_1918_)) as u8;
                    if v_isSharedCheck_1952_ == 0 {
                        v___x_1921_ = v___x_1918_;
                        v_isShared_1922_ = v_isSharedCheck_1952_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1919_);
                        lean_dec(v___x_1918_);
                        v___x_1921_ = lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1952_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1919_) == 1 {
                    lean_del_object(v___x_1921_);
                    v_val_1923_ = lean_ctor_get(v_a_1919_, 0);
                    lean_inc(v_val_1923_);
                    lean_dec_ref_known(v_a_1919_, 1);
                    v___x_1924_ = l_Lean_Expr_appArg_x21(v_e_1909_);
                    v___x_1925_ = l_String_fromExpr_x3f___redArg(v___x_1924_);
                    v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
                    v_isSharedCheck_1947_ = (!lean_is_exclusive(v___x_1925_)) as u8;
                    if v_isSharedCheck_1947_ == 0 {
                        v___x_1928_ = v___x_1925_;
                        v_isShared_1929_ = v_isSharedCheck_1947_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1926_);
                        lean_dec(v___x_1925_);
                        v___x_1928_ = lean_box(0);
                        v_isShared_1929_ = v_isSharedCheck_1947_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1919_);
                    v___x_1948_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_1922_ == 0 {
                        lean_ctor_set(v___x_1921_, 0, v___x_1948_);
                        v___x_1950_ = v___x_1921_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
                        v___x_1950_ = v_reuseFailAlloc_1951_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1926_) == 1 {
                    v_val_1930_ = lean_ctor_get(v_a_1926_, 0);
                    v_isSharedCheck_1942_ = (!lean_is_exclusive(v_a_1926_)) as u8;
                    if v_isSharedCheck_1942_ == 0 {
                        v___x_1932_ = v_a_1926_;
                        v_isShared_1933_ = v_isSharedCheck_1942_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1930_);
                        lean_dec(v_a_1926_);
                        v___x_1932_ = lean_box(0);
                        v_isShared_1933_ = v_isSharedCheck_1942_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1926_);
                    lean_dec(v_val_1923_);
                    v___x_1943_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_1929_ == 0 {
                        lean_ctor_set(v___x_1928_, 0, v___x_1943_);
                        v___x_1945_ = v___x_1928_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
                        v___x_1945_ = v_reuseFailAlloc_1946_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1934_ = lean_string_append(v_val_1923_, v_val_1930_);
                lean_dec(v_val_1930_);
                v___x_1935_ = l_Lean_mkStrLit(v___x_1934_);
                if v_isShared_1933_ == 0 {
                    lean_ctor_set_tag(v___x_1932_, 0);
                    lean_ctor_set(v___x_1932_, 0, v___x_1935_);
                    v___x_1937_ = v___x_1932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1935_);
                    v___x_1937_ = v_reuseFailAlloc_1941_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1929_ == 0 {
                    lean_ctor_set(v___x_1928_, 0, v___x_1937_);
                    v___x_1939_ = v___x_1928_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
                    v___x_1939_ = v_reuseFailAlloc_1940_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1939_;
            }
            6 => {
                return v___x_1945_;
            }
            7 => {
                return v___x_1950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceAppend___redArg___boxed(
    mut v_e_1953_: *mut LeanObject,
    mut v_a_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1955_: *mut LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_String_reduceAppend___redArg(v_e_1953_);
    lean_dec_ref(v_e_1953_);
    return v_res_1955_;
}
pub unsafe fn l_String_reduceAppend(
    mut v_e_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
    mut v_a_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_String_reduceAppend___redArg(v_e_1956_);
    return v___x_1965_;
}
pub unsafe fn l_String_reduceAppend___boxed(
    mut v_e_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_String_reduceAppend(
        v_e_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_,
    );
    lean_dec(v_a_1973_);
    lean_dec_ref(v_a_1972_);
    lean_dec(v_a_1971_);
    lean_dec_ref(v_a_1970_);
    lean_dec(v_a_1969_);
    lean_dec_ref(v_a_1968_);
    lean_dec(v_a_1967_);
    lean_dec_ref(v_e_1966_);
    return v_res_1975_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_()
-> *mut LeanObject {
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    v___x_2002_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_;
    v___x_2003_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__6_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_;
    v___x_2004_ = lean_alloc_closure(
        l_String_reduceAppend___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2005_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2002_, v___x_2003_, v___x_2004_);
    return v___x_2005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19____boxed(
    mut v_a_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2007_: *mut LeanObject = core::ptr::null_mut();
    v_res_2007_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_();
    return v_res_2007_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_()
-> *mut LeanObject {
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    v___x_2008_ = lean_alloc_closure(
        l_String_reduceAppend___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2009_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2009_, 0, v___x_2008_);
    return v___x_2009_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_()
-> *mut LeanObject {
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    v___x_2011_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_;
    v___x_2012_ = 1;
    v___x_2013_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_);
    v___x_2014_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2011_, v___x_2012_, v___x_2013_);
    return v___x_2014_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21____boxed(
    mut v_a_2015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2016_: *mut LeanObject = core::ptr::null_mut();
    v_res_2016_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_();
    return v_res_2016_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_()
-> *mut LeanObject {
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    v___x_2018_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_;
    v___x_2019_ = 1;
    v___x_2020_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_);
    v___x_2021_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2018_, v___x_2019_, v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23____boxed(
    mut v_a_2022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2023_: *mut LeanObject = core::ptr::null_mut();
    v_res_2023_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_();
    return v_res_2023_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(
    mut v_e_2033_: *mut LeanObject,
    mut v_s_2034_: *mut LeanObject,
    mut v_a_2035_: *mut LeanObject,
    mut v_a_2036_: *mut LeanObject,
    mut v_a_2037_: *mut LeanObject,
    mut v_a_2038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v_val_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u32 = 0;
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2064_: u8 = 0;
    let mut v_a_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2040_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2;
                v___x_2041_ = lean_unsigned_to_nat(1);
                v___x_2042_ = l_Lean_Expr_isAppOfArity(v_e_2033_, v___x_2040_, v___x_2041_);
                if v___x_2042_ == 0 {
                    v___x_2043_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4;
                    v___x_2044_ = lean_unsigned_to_nat(3);
                    v___x_2045_ = l_Lean_Expr_isAppOfArity(v_e_2033_, v___x_2043_, v___x_2044_);
                    if v___x_2045_ == 0 {
                        lean_dec_ref(v_s_2034_);
                        lean_dec_ref(v_e_2033_);
                        v___x_2046_ = l_String_reduceAppend___redArg___closed__3;
                        v___x_2047_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2047_, 0, v___x_2046_);
                        return v___x_2047_;
                    } else {
                        v___x_2048_ = l_Lean_Expr_appFn_x21(v_e_2033_);
                        v___x_2049_ = l_Lean_Expr_appArg_x21(v___x_2048_);
                        lean_dec_ref(v___x_2048_);
                        v___x_2050_ = l_Lean_Meta_getCharValue_x3f(
                            v___x_2049_,
                            v_a_2035_,
                            v_a_2036_,
                            v_a_2037_,
                            v_a_2038_,
                        );
                        if lean_obj_tag(v___x_2050_) == 0 {
                            v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
                            v_isSharedCheck_2064_ = (!lean_is_exclusive(v___x_2050_)) as u8;
                            if v_isSharedCheck_2064_ == 0 {
                                v___x_2053_ = v___x_2050_;
                                v_isShared_2054_ = v_isSharedCheck_2064_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2051_);
                                lean_dec(v___x_2050_);
                                v___x_2053_ = lean_box(0);
                                v_isShared_2054_ = v_isSharedCheck_2064_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_s_2034_);
                            lean_dec_ref(v_e_2033_);
                            v_a_2065_ = lean_ctor_get(v___x_2050_, 0);
                            v_isSharedCheck_2072_ = (!lean_is_exclusive(v___x_2050_)) as u8;
                            if v_isSharedCheck_2072_ == 0 {
                                v___x_2067_ = v___x_2050_;
                                v_isShared_2068_ = v_isSharedCheck_2072_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2065_);
                                lean_dec(v___x_2050_);
                                v___x_2067_ = lean_box(0);
                                v_isShared_2068_ = v_isSharedCheck_2072_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_2033_);
                    v___x_2073_ = l_Lean_mkStrLit(v_s_2034_);
                    v___x_2074_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2074_, 0, v___x_2073_);
                    v___x_2075_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2075_, 0, v___x_2074_);
                    return v___x_2075_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_2051_) == 1 {
                    lean_del_object(v___x_2053_);
                    v_val_2055_ = lean_ctor_get(v_a_2051_, 0);
                    lean_inc(v_val_2055_);
                    lean_dec_ref_known(v_a_2051_, 1);
                    v___x_2056_ = l_Lean_Expr_appArg_x21(v_e_2033_);
                    lean_dec_ref(v_e_2033_);
                    v___x_2057_ = lean_unbox_uint32(v_val_2055_);
                    lean_dec(v_val_2055_);
                    v___x_2058_ = lean_string_push(v_s_2034_, v___x_2057_);
                    v_e_2033_ = v___x_2056_;
                    v_s_2034_ = v___x_2058_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_2051_);
                    lean_dec_ref(v_s_2034_);
                    lean_dec_ref(v_e_2033_);
                    v___x_2060_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2054_ == 0 {
                        lean_ctor_set(v___x_2053_, 0, v___x_2060_);
                        v___x_2062_ = v___x_2053_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
                        v___x_2062_ = v_reuseFailAlloc_2063_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2062_;
            }
            3 => {
                if v_isShared_2068_ == 0 {
                    v___x_2070_ = v___x_2067_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
                    v___x_2070_ = v_reuseFailAlloc_2071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___boxed(
    mut v_e_2076_: *mut LeanObject,
    mut v_s_2077_: *mut LeanObject,
    mut v_a_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2083_: *mut LeanObject = core::ptr::null_mut();
    v_res_2083_ =
        l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(
            v_e_2076_, v_s_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_,
        );
    lean_dec(v_a_2081_);
    lean_dec_ref(v_a_2080_);
    lean_dec(v_a_2079_);
    lean_dec_ref(v_a_2078_);
    return v_res_2083_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar(
    mut v_e_2084_: *mut LeanObject,
    mut v_s_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
    mut v_a_2091_: *mut LeanObject,
    mut v_a_2092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    v___x_2094_ =
        l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(
            v_e_2084_, v_s_2085_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_,
        );
    return v___x_2094_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___boxed(
    mut v_e_2095_: *mut LeanObject,
    mut v_s_2096_: *mut LeanObject,
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
    mut v_a_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
    mut v_a_2103_: *mut LeanObject,
    mut v_a_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2105_: *mut LeanObject = core::ptr::null_mut();
    v_res_2105_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar(
        v_e_2095_, v_s_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_,
        v_a_2103_,
    );
    lean_dec(v_a_2103_);
    lean_dec_ref(v_a_2102_);
    lean_dec(v_a_2101_);
    lean_dec_ref(v_a_2100_);
    lean_dec(v_a_2099_);
    lean_dec_ref(v_a_2098_);
    lean_dec(v_a_2097_);
    return v_res_2105_;
}
pub unsafe fn l_String_reduceOfList___redArg(
    mut v_e_2111_: *mut LeanObject,
    mut v_a_2112_: *mut LeanObject,
    mut v_a_2113_: *mut LeanObject,
    mut v_a_2114_: *mut LeanObject,
    mut v_a_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u8 = 0;
    v___x_2117_ = l_String_reduceOfList___redArg___closed__1;
    v___x_2118_ = lean_unsigned_to_nat(1);
    v___x_2119_ = l_Lean_Expr_isAppOfArity(v_e_2111_, v___x_2117_, v___x_2118_);
    if v___x_2119_ == 0 {
        let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
        v___x_2120_ = l_String_reduceAppend___redArg___closed__3;
        v___x_2121_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2121_, 0, v___x_2120_);
        return v___x_2121_;
    } else {
        let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
        v___x_2122_ = l_Lean_Expr_appArg_x21(v_e_2111_);
        v___x_2123_ = l_String_reduceOfList___redArg___closed__2;
        v___x_2124_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg(v___x_2122_, v___x_2123_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
        return v___x_2124_;
    }
}
pub unsafe fn l_String_reduceOfList___redArg___boxed(
    mut v_e_2125_: *mut LeanObject,
    mut v_a_2126_: *mut LeanObject,
    mut v_a_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
    mut v_a_2129_: *mut LeanObject,
    mut v_a_2130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2131_: *mut LeanObject = core::ptr::null_mut();
    v_res_2131_ =
        l_String_reduceOfList___redArg(v_e_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_);
    lean_dec(v_a_2129_);
    lean_dec_ref(v_a_2128_);
    lean_dec(v_a_2127_);
    lean_dec_ref(v_a_2126_);
    lean_dec_ref(v_e_2125_);
    return v_res_2131_;
}
pub unsafe fn l_String_reduceOfList(
    mut v_e_2132_: *mut LeanObject,
    mut v_a_2133_: *mut LeanObject,
    mut v_a_2134_: *mut LeanObject,
    mut v_a_2135_: *mut LeanObject,
    mut v_a_2136_: *mut LeanObject,
    mut v_a_2137_: *mut LeanObject,
    mut v_a_2138_: *mut LeanObject,
    mut v_a_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    v___x_2141_ =
        l_String_reduceOfList___redArg(v_e_2132_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
    return v___x_2141_;
}
pub unsafe fn l_String_reduceOfList___boxed(
    mut v_e_2142_: *mut LeanObject,
    mut v_a_2143_: *mut LeanObject,
    mut v_a_2144_: *mut LeanObject,
    mut v_a_2145_: *mut LeanObject,
    mut v_a_2146_: *mut LeanObject,
    mut v_a_2147_: *mut LeanObject,
    mut v_a_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2151_: *mut LeanObject = core::ptr::null_mut();
    v_res_2151_ = l_String_reduceOfList(
        v_e_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_,
    );
    lean_dec(v_a_2149_);
    lean_dec_ref(v_a_2148_);
    lean_dec(v_a_2147_);
    lean_dec_ref(v_a_2146_);
    lean_dec(v_a_2145_);
    lean_dec_ref(v_a_2144_);
    lean_dec(v_a_2143_);
    lean_dec_ref(v_e_2142_);
    return v_res_2151_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_()
-> *mut LeanObject {
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    v___x_2166_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_;
    v___x_2167_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_;
    v___x_2168_ = lean_alloc_closure(
        l_String_reduceOfList___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2169_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2166_, v___x_2167_, v___x_2168_);
    return v___x_2169_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13____boxed(
    mut v_a_2170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2171_: *mut LeanObject = core::ptr::null_mut();
    v_res_2171_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_();
    return v_res_2171_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    v___x_2172_ = lean_alloc_closure(
        l_String_reduceOfList___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2173_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2173_, 0, v___x_2172_);
    return v___x_2173_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    v___x_2175_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_;
    v___x_2176_ = 1;
    v___x_2177_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_);
    v___x_2178_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2175_, v___x_2176_, v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15____boxed(
    mut v_a_2179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2180_: *mut LeanObject = core::ptr::null_mut();
    v_res_2180_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_();
    return v_res_2180_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    v___x_2182_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_;
    v___x_2183_ = 1;
    v___x_2184_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_);
    v___x_2185_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2182_, v___x_2183_, v___x_2184_);
    return v___x_2185_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17____boxed(
    mut v_a_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2187_: *mut LeanObject = core::ptr::null_mut();
    v_res_2187_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_();
    return v_res_2187_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    v___x_2193_ = lean_box(0);
    v___x_2194_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__2;
    v___x_2195_ = l_Lean_mkConst(v___x_2194_, v___x_2193_);
    return v___x_2195_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(
    mut v_nilFn_2196_: *mut LeanObject,
    mut v_consFn_2197_: *mut LeanObject,
    mut v_x_2198_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2198_) == 0 {
        lean_dec_ref(v_consFn_2197_);
        lean_inc_ref(v_nilFn_2196_);
        return v_nilFn_2196_;
    } else {
        let mut v_head_2199_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2202_: u32 = 0;
        let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
        v_head_2199_ = lean_ctor_get(v_x_2198_, 0);
        v_tail_2200_ = lean_ctor_get(v_x_2198_, 1);
        v___x_2201_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3);
        v___x_2202_ = lean_unbox_uint32(v_head_2199_);
        v___x_2203_ = lean_uint32_to_nat(v___x_2202_);
        v___x_2204_ = l_Lean_mkRawNatLit(v___x_2203_);
        v___x_2205_ = l_Lean_Expr_app___override(v___x_2201_, v___x_2204_);
        lean_inc_ref(v_consFn_2197_);
        v___x_2206_ =
            l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(
                v_nilFn_2196_,
                v_consFn_2197_,
                v_tail_2200_,
            );
        v___x_2207_ = l_Lean_mkAppB(v_consFn_2197_, v___x_2205_, v___x_2206_);
        return v___x_2207_;
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___boxed(
    mut v_nilFn_2208_: *mut LeanObject,
    mut v_consFn_2209_: *mut LeanObject,
    mut v_x_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2211_: *mut LeanObject = core::ptr::null_mut();
    v_res_2211_ =
        l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(
            v_nilFn_2208_,
            v_consFn_2209_,
            v_x_2210_,
        );
    lean_dec(v_x_2210_);
    lean_dec_ref(v_nilFn_2208_);
    return v_res_2211_;
}
pub unsafe fn _init_l_String_reduceToList___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    v___x_2218_ = lean_box(0);
    v___x_2219_ = l_String_reduceToList___redArg___closed__2;
    v___x_2220_ = l_Lean_mkConst(v___x_2219_, v___x_2218_);
    return v___x_2220_;
}
pub unsafe fn _init_l_String_reduceToList___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    v___x_2224_ = l_String_reduceToList___redArg___closed__4;
    v___x_2225_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__2;
    v___x_2226_ = l_Lean_mkConst(v___x_2225_, v___x_2224_);
    return v___x_2226_;
}
pub unsafe fn _init_l_String_reduceToList___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nil_2229_: *mut LeanObject = core::ptr::null_mut();
    v___x_2227_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__3),
        core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__3_once),
        _init_l_String_reduceToList___redArg___closed__3,
    );
    v___x_2228_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__5),
        core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__5_once),
        _init_l_String_reduceToList___redArg___closed__5,
    );
    v_nil_2229_ = l_Lean_Expr_app___override(v___x_2228_, v___x_2227_);
    return v_nil_2229_;
}
pub unsafe fn _init_l_String_reduceToList___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_String_reduceToList___redArg___closed__4;
    v___x_2231_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceListChar___redArg___closed__4;
    v___x_2232_ = l_Lean_mkConst(v___x_2231_, v___x_2230_);
    return v___x_2232_;
}
pub unsafe fn _init_l_String_reduceToList___redArg___closed__8() -> *mut LeanObject {
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cons_2235_: *mut LeanObject = core::ptr::null_mut();
    v___x_2233_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__3),
        core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__3_once),
        _init_l_String_reduceToList___redArg___closed__3,
    );
    v___x_2234_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__7),
        core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__7_once),
        _init_l_String_reduceToList___redArg___closed__7,
    );
    v_cons_2235_ = l_Lean_Expr_app___override(v___x_2234_, v___x_2233_);
    return v_cons_2235_;
}
pub unsafe fn l_String_reduceToList___redArg(mut v_e_2236_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v_val_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2252_: u8 = 0;
    let mut v_nil_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cons_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2238_ = l_String_reduceToList___redArg___closed__1;
                v___x_2239_ = lean_unsigned_to_nat(1);
                v___x_2240_ = l_Lean_Expr_isAppOfArity(v_e_2236_, v___x_2238_, v___x_2239_);
                if v___x_2240_ == 0 {
                    v___x_2241_ = l_String_reduceAppend___redArg___closed__3;
                    v___x_2242_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2242_, 0, v___x_2241_);
                    return v___x_2242_;
                } else {
                    v___x_2243_ = l_Lean_Expr_appArg_x21(v_e_2236_);
                    v___x_2244_ = l_String_fromExpr_x3f___redArg(v___x_2243_);
                    v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
                    v_isSharedCheck_2268_ = (!lean_is_exclusive(v___x_2244_)) as u8;
                    if v_isSharedCheck_2268_ == 0 {
                        v___x_2247_ = v___x_2244_;
                        v_isShared_2248_ = v_isSharedCheck_2268_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2245_);
                        lean_dec(v___x_2244_);
                        v___x_2247_ = lean_box(0);
                        v_isShared_2248_ = v_isSharedCheck_2268_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2245_) == 1 {
                    v_val_2249_ = lean_ctor_get(v_a_2245_, 0);
                    v_isSharedCheck_2263_ = (!lean_is_exclusive(v_a_2245_)) as u8;
                    if v_isSharedCheck_2263_ == 0 {
                        v___x_2251_ = v_a_2245_;
                        v_isShared_2252_ = v_isSharedCheck_2263_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2249_);
                        lean_dec(v_a_2245_);
                        v___x_2251_ = lean_box(0);
                        v_isShared_2252_ = v_isSharedCheck_2263_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2245_);
                    v___x_2264_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2248_ == 0 {
                        lean_ctor_set(v___x_2247_, 0, v___x_2264_);
                        v___x_2266_ = v___x_2247_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
                        v___x_2266_ = v_reuseFailAlloc_2267_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_nil_2253_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__6),
                    core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__6_once),
                    _init_l_String_reduceToList___redArg___closed__6,
                );
                v_cons_2254_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__8),
                    core::ptr::addr_of_mut!(l_String_reduceToList___redArg___closed__8_once),
                    _init_l_String_reduceToList___redArg___closed__8,
                );
                v___x_2255_ = lean_string_data(v_val_2249_);
                v___x_2256_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0(v_nil_2253_, v_cons_2254_, v___x_2255_);
                lean_dec(v___x_2255_);
                if v_isShared_2252_ == 0 {
                    lean_ctor_set_tag(v___x_2251_, 0);
                    lean_ctor_set(v___x_2251_, 0, v___x_2256_);
                    v___x_2258_ = v___x_2251_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2256_);
                    v___x_2258_ = v_reuseFailAlloc_2262_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2248_ == 0 {
                    lean_ctor_set(v___x_2247_, 0, v___x_2258_);
                    v___x_2260_ = v___x_2247_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
                    v___x_2260_ = v_reuseFailAlloc_2261_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2260_;
            }
            5 => {
                return v___x_2266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceToList___redArg___boxed(
    mut v_e_2269_: *mut LeanObject,
    mut v_a_2270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2271_: *mut LeanObject = core::ptr::null_mut();
    v_res_2271_ = l_String_reduceToList___redArg(v_e_2269_);
    lean_dec_ref(v_e_2269_);
    return v_res_2271_;
}
pub unsafe fn l_String_reduceToList(
    mut v_e_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
    mut v_a_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_a_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_String_reduceToList___redArg(v_e_2272_);
    return v___x_2281_;
}
pub unsafe fn l_String_reduceToList___boxed(
    mut v_e_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
    mut v_a_2289_: *mut LeanObject,
    mut v_a_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2291_: *mut LeanObject = core::ptr::null_mut();
    v_res_2291_ = l_String_reduceToList(
        v_e_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_,
    );
    lean_dec(v_a_2289_);
    lean_dec_ref(v_a_2288_);
    lean_dec(v_a_2287_);
    lean_dec_ref(v_a_2286_);
    lean_dec(v_a_2285_);
    lean_dec_ref(v_a_2284_);
    lean_dec(v_a_2283_);
    lean_dec_ref(v_e_2282_);
    return v_res_2291_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_()
-> *mut LeanObject {
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    v___x_2306_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_;
    v___x_2307_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_;
    v___x_2308_ = lean_alloc_closure(
        l_String_reduceToList___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2309_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2306_, v___x_2307_, v___x_2308_);
    return v___x_2309_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13____boxed(
    mut v_a_2310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2311_: *mut LeanObject = core::ptr::null_mut();
    v_res_2311_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_();
    return v_res_2311_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    v___x_2312_ = lean_alloc_closure(
        l_String_reduceToList___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2313_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2313_, 0, v___x_2312_);
    return v___x_2313_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    v___x_2315_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_;
    v___x_2316_ = 1;
    v___x_2317_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_);
    v___x_2318_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2315_, v___x_2316_, v___x_2317_);
    return v___x_2318_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15____boxed(
    mut v_a_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2320_: *mut LeanObject = core::ptr::null_mut();
    v_res_2320_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_();
    return v_res_2320_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    v___x_2322_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_;
    v___x_2323_ = 1;
    v___x_2324_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_);
    v___x_2325_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2322_, v___x_2323_, v___x_2324_);
    return v___x_2325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17____boxed(
    mut v_a_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2327_: *mut LeanObject = core::ptr::null_mut();
    v_res_2327_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_();
    return v_res_2327_;
}
pub unsafe fn l_String_reducePush___redArg(
    mut v_e_2332_: *mut LeanObject,
    mut v_a_2333_: *mut LeanObject,
    mut v_a_2334_: *mut LeanObject,
    mut v_a_2335_: *mut LeanObject,
    mut v_a_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: u8 = 0;
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v_val_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v_val_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v___x_2361_: u32 = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2375_: u8 = 0;
    let mut v_a_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2383_: u8 = 0;
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2338_ = l_String_reducePush___redArg___closed__1;
                v___x_2339_ = lean_unsigned_to_nat(2);
                v___x_2340_ = l_Lean_Expr_isAppOfArity(v_e_2332_, v___x_2338_, v___x_2339_);
                if v___x_2340_ == 0 {
                    v___x_2341_ = l_String_reduceAppend___redArg___closed__3;
                    v___x_2342_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2342_, 0, v___x_2341_);
                    return v___x_2342_;
                } else {
                    v___x_2343_ = l_Lean_Expr_appFn_x21(v_e_2332_);
                    v___x_2344_ = l_Lean_Expr_appArg_x21(v___x_2343_);
                    lean_dec_ref(v___x_2343_);
                    v___x_2345_ = l_String_fromExpr_x3f___redArg(v___x_2344_);
                    v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
                    v_isSharedCheck_2388_ = (!lean_is_exclusive(v___x_2345_)) as u8;
                    if v_isSharedCheck_2388_ == 0 {
                        v___x_2348_ = v___x_2345_;
                        v_isShared_2349_ = v_isSharedCheck_2388_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2346_);
                        lean_dec(v___x_2345_);
                        v___x_2348_ = lean_box(0);
                        v_isShared_2349_ = v_isSharedCheck_2388_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2346_) == 1 {
                    lean_del_object(v___x_2348_);
                    v_val_2350_ = lean_ctor_get(v_a_2346_, 0);
                    lean_inc(v_val_2350_);
                    lean_dec_ref_known(v_a_2346_, 1);
                    v___x_2351_ = l_Lean_Expr_appArg_x21(v_e_2332_);
                    v___x_2352_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_2351_,
                        v_a_2333_,
                        v_a_2334_,
                        v_a_2335_,
                        v_a_2336_,
                    );
                    if lean_obj_tag(v___x_2352_) == 0 {
                        v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
                        v_isSharedCheck_2375_ = (!lean_is_exclusive(v___x_2352_)) as u8;
                        if v_isSharedCheck_2375_ == 0 {
                            v___x_2355_ = v___x_2352_;
                            v_isShared_2356_ = v_isSharedCheck_2375_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2353_);
                            lean_dec(v___x_2352_);
                            v___x_2355_ = lean_box(0);
                            v_isShared_2356_ = v_isSharedCheck_2375_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_2350_);
                        v_a_2376_ = lean_ctor_get(v___x_2352_, 0);
                        v_isSharedCheck_2383_ = (!lean_is_exclusive(v___x_2352_)) as u8;
                        if v_isSharedCheck_2383_ == 0 {
                            v___x_2378_ = v___x_2352_;
                            v_isShared_2379_ = v_isSharedCheck_2383_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2376_);
                            lean_dec(v___x_2352_);
                            v___x_2378_ = lean_box(0);
                            v_isShared_2379_ = v_isSharedCheck_2383_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2346_);
                    v___x_2384_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2349_ == 0 {
                        lean_ctor_set(v___x_2348_, 0, v___x_2384_);
                        v___x_2386_ = v___x_2348_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2384_);
                        v___x_2386_ = v_reuseFailAlloc_2387_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2353_) == 1 {
                    v_val_2357_ = lean_ctor_get(v_a_2353_, 0);
                    v_isSharedCheck_2370_ = (!lean_is_exclusive(v_a_2353_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2359_ = v_a_2353_;
                        v_isShared_2360_ = v_isSharedCheck_2370_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2357_);
                        lean_dec(v_a_2353_);
                        v___x_2359_ = lean_box(0);
                        v_isShared_2360_ = v_isSharedCheck_2370_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2353_);
                    lean_dec(v_val_2350_);
                    v___x_2371_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2356_ == 0 {
                        lean_ctor_set(v___x_2355_, 0, v___x_2371_);
                        v___x_2373_ = v___x_2355_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
                        v___x_2373_ = v_reuseFailAlloc_2374_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2361_ = lean_unbox_uint32(v_val_2357_);
                lean_dec(v_val_2357_);
                v___x_2362_ = lean_string_push(v_val_2350_, v___x_2361_);
                v___x_2363_ = l_Lean_mkStrLit(v___x_2362_);
                if v_isShared_2360_ == 0 {
                    lean_ctor_set_tag(v___x_2359_, 0);
                    lean_ctor_set(v___x_2359_, 0, v___x_2363_);
                    v___x_2365_ = v___x_2359_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2363_);
                    v___x_2365_ = v_reuseFailAlloc_2369_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2356_ == 0 {
                    lean_ctor_set(v___x_2355_, 0, v___x_2365_);
                    v___x_2367_ = v___x_2355_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
                    v___x_2367_ = v_reuseFailAlloc_2368_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2367_;
            }
            6 => {
                return v___x_2373_;
            }
            7 => {
                if v_isShared_2379_ == 0 {
                    v___x_2381_ = v___x_2378_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
                    v___x_2381_ = v_reuseFailAlloc_2382_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2381_;
            }
            9 => {
                return v___x_2386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reducePush___redArg___boxed(
    mut v_e_2389_: *mut LeanObject,
    mut v_a_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
    mut v_a_2393_: *mut LeanObject,
    mut v_a_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2395_: *mut LeanObject = core::ptr::null_mut();
    v_res_2395_ =
        l_String_reducePush___redArg(v_e_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
    lean_dec(v_a_2393_);
    lean_dec_ref(v_a_2392_);
    lean_dec(v_a_2391_);
    lean_dec_ref(v_a_2390_);
    lean_dec_ref(v_e_2389_);
    return v_res_2395_;
}
pub unsafe fn l_String_reducePush(
    mut v_e_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
    mut v_a_2399_: *mut LeanObject,
    mut v_a_2400_: *mut LeanObject,
    mut v_a_2401_: *mut LeanObject,
    mut v_a_2402_: *mut LeanObject,
    mut v_a_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    v___x_2405_ =
        l_String_reducePush___redArg(v_e_2396_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
    return v___x_2405_;
}
pub unsafe fn l_String_reducePush___boxed(
    mut v_e_2406_: *mut LeanObject,
    mut v_a_2407_: *mut LeanObject,
    mut v_a_2408_: *mut LeanObject,
    mut v_a_2409_: *mut LeanObject,
    mut v_a_2410_: *mut LeanObject,
    mut v_a_2411_: *mut LeanObject,
    mut v_a_2412_: *mut LeanObject,
    mut v_a_2413_: *mut LeanObject,
    mut v_a_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2415_: *mut LeanObject = core::ptr::null_mut();
    v_res_2415_ = l_String_reducePush(
        v_e_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_,
    );
    lean_dec(v_a_2413_);
    lean_dec_ref(v_a_2412_);
    lean_dec(v_a_2411_);
    lean_dec_ref(v_a_2410_);
    lean_dec(v_a_2409_);
    lean_dec_ref(v_a_2408_);
    lean_dec(v_a_2407_);
    lean_dec_ref(v_e_2406_);
    return v_res_2415_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_()
-> *mut LeanObject {
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    v___x_2431_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_;
    v___x_2432_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_;
    v___x_2433_ = lean_alloc_closure(l_String_reducePush___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_2434_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2431_, v___x_2432_, v___x_2433_);
    return v___x_2434_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14____boxed(
    mut v_a_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2436_: *mut LeanObject = core::ptr::null_mut();
    v_res_2436_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_();
    return v_res_2436_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_()
-> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = lean_alloc_closure(l_String_reducePush___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_2438_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2438_, 0, v___x_2437_);
    return v___x_2438_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_()
-> *mut LeanObject {
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    v___x_2440_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_;
    v___x_2441_ = 1;
    v___x_2442_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_);
    v___x_2443_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2440_, v___x_2441_, v___x_2442_);
    return v___x_2443_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16____boxed(
    mut v_a_2444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2445_: *mut LeanObject = core::ptr::null_mut();
    v_res_2445_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_();
    return v_res_2445_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_()
-> *mut LeanObject {
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    v___x_2447_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_;
    v___x_2448_ = 1;
    v___x_2449_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_);
    v___x_2450_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2447_, v___x_2448_, v___x_2449_);
    return v___x_2450_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18____boxed(
    mut v_a_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2452_: *mut LeanObject = core::ptr::null_mut();
    v_res_2452_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_();
    return v_res_2452_;
}
pub unsafe fn l_String_reduceSingleton___redArg(
    mut v_e_2457_: *mut LeanObject,
    mut v_a_2458_: *mut LeanObject,
    mut v_a_2459_: *mut LeanObject,
    mut v_a_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2473_: u8 = 0;
    let mut v_val_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2477_: u8 = 0;
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: u32 = 0;
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v_a_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2463_ = l_String_reduceSingleton___redArg___closed__1;
                v___x_2464_ = lean_unsigned_to_nat(1);
                v___x_2465_ = l_Lean_Expr_isAppOfArity(v_e_2457_, v___x_2463_, v___x_2464_);
                if v___x_2465_ == 0 {
                    v___x_2466_ = l_String_reduceAppend___redArg___closed__3;
                    v___x_2467_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2467_, 0, v___x_2466_);
                    return v___x_2467_;
                } else {
                    v___x_2468_ = l_Lean_Expr_appArg_x21(v_e_2457_);
                    v___x_2469_ = l_Lean_Meta_getCharValue_x3f(
                        v___x_2468_,
                        v_a_2458_,
                        v_a_2459_,
                        v_a_2460_,
                        v_a_2461_,
                    );
                    if lean_obj_tag(v___x_2469_) == 0 {
                        v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
                        v_isSharedCheck_2493_ = (!lean_is_exclusive(v___x_2469_)) as u8;
                        if v_isSharedCheck_2493_ == 0 {
                            v___x_2472_ = v___x_2469_;
                            v_isShared_2473_ = v_isSharedCheck_2493_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2470_);
                            lean_dec(v___x_2469_);
                            v___x_2472_ = lean_box(0);
                            v_isShared_2473_ = v_isSharedCheck_2493_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2494_ = lean_ctor_get(v___x_2469_, 0);
                        v_isSharedCheck_2501_ = (!lean_is_exclusive(v___x_2469_)) as u8;
                        if v_isSharedCheck_2501_ == 0 {
                            v___x_2496_ = v___x_2469_;
                            v_isShared_2497_ = v_isSharedCheck_2501_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2494_);
                            lean_dec(v___x_2469_);
                            v___x_2496_ = lean_box(0);
                            v_isShared_2497_ = v_isSharedCheck_2501_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2470_) == 1 {
                    v_val_2474_ = lean_ctor_get(v_a_2470_, 0);
                    v_isSharedCheck_2488_ = (!lean_is_exclusive(v_a_2470_)) as u8;
                    if v_isSharedCheck_2488_ == 0 {
                        v___x_2476_ = v_a_2470_;
                        v_isShared_2477_ = v_isSharedCheck_2488_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2474_);
                        lean_dec(v_a_2470_);
                        v___x_2476_ = lean_box(0);
                        v_isShared_2477_ = v_isSharedCheck_2488_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2470_);
                    v___x_2489_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2473_ == 0 {
                        lean_ctor_set(v___x_2472_, 0, v___x_2489_);
                        v___x_2491_ = v___x_2472_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
                        v___x_2491_ = v_reuseFailAlloc_2492_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2478_ = l_String_reduceOfList___redArg___closed__2;
                v___x_2479_ = lean_unbox_uint32(v_val_2474_);
                lean_dec(v_val_2474_);
                v___x_2480_ = lean_string_push(v___x_2478_, v___x_2479_);
                v___x_2481_ = l_Lean_mkStrLit(v___x_2480_);
                if v_isShared_2477_ == 0 {
                    lean_ctor_set_tag(v___x_2476_, 0);
                    lean_ctor_set(v___x_2476_, 0, v___x_2481_);
                    v___x_2483_ = v___x_2476_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2481_);
                    v___x_2483_ = v_reuseFailAlloc_2487_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2473_ == 0 {
                    lean_ctor_set(v___x_2472_, 0, v___x_2483_);
                    v___x_2485_ = v___x_2472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2483_);
                    v___x_2485_ = v_reuseFailAlloc_2486_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2485_;
            }
            5 => {
                return v___x_2491_;
            }
            6 => {
                if v_isShared_2497_ == 0 {
                    v___x_2499_ = v___x_2496_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceSingleton___redArg___boxed(
    mut v_e_2502_: *mut LeanObject,
    mut v_a_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
    mut v_a_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2508_: *mut LeanObject = core::ptr::null_mut();
    v_res_2508_ =
        l_String_reduceSingleton___redArg(v_e_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
    lean_dec(v_a_2506_);
    lean_dec_ref(v_a_2505_);
    lean_dec(v_a_2504_);
    lean_dec_ref(v_a_2503_);
    lean_dec_ref(v_e_2502_);
    return v_res_2508_;
}
pub unsafe fn l_String_reduceSingleton(
    mut v_e_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
    mut v_a_2515_: *mut LeanObject,
    mut v_a_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    v___x_2518_ =
        l_String_reduceSingleton___redArg(v_e_2509_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
    return v___x_2518_;
}
pub unsafe fn l_String_reduceSingleton___boxed(
    mut v_e_2519_: *mut LeanObject,
    mut v_a_2520_: *mut LeanObject,
    mut v_a_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
    mut v_a_2523_: *mut LeanObject,
    mut v_a_2524_: *mut LeanObject,
    mut v_a_2525_: *mut LeanObject,
    mut v_a_2526_: *mut LeanObject,
    mut v_a_2527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2528_: *mut LeanObject = core::ptr::null_mut();
    v_res_2528_ = l_String_reduceSingleton(
        v_e_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_,
    );
    lean_dec(v_a_2526_);
    lean_dec_ref(v_a_2525_);
    lean_dec(v_a_2524_);
    lean_dec_ref(v_a_2523_);
    lean_dec(v_a_2522_);
    lean_dec_ref(v_a_2521_);
    lean_dec(v_a_2520_);
    lean_dec_ref(v_e_2519_);
    return v_res_2528_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_()
-> *mut LeanObject {
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    v___x_2543_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_;
    v___x_2544_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_;
    v___x_2545_ = lean_alloc_closure(
        l_String_reduceSingleton___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2546_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2543_, v___x_2544_, v___x_2545_);
    return v___x_2546_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13____boxed(
    mut v_a_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2548_: *mut LeanObject = core::ptr::null_mut();
    v_res_2548_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_();
    return v_res_2548_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    v___x_2549_ = lean_alloc_closure(
        l_String_reduceSingleton___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2550_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2550_, 0, v___x_2549_);
    return v___x_2550_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_()
-> *mut LeanObject {
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    v___x_2552_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_;
    v___x_2553_ = 1;
    v___x_2554_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_);
    v___x_2555_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2552_, v___x_2553_, v___x_2554_);
    return v___x_2555_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15____boxed(
    mut v_a_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2557_: *mut LeanObject = core::ptr::null_mut();
    v_res_2557_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_();
    return v_res_2557_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_()
-> *mut LeanObject {
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: u8 = 0;
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    v___x_2559_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_;
    v___x_2560_ = 1;
    v___x_2561_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_);
    v___x_2562_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2559_, v___x_2560_, v___x_2561_);
    return v___x_2562_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17____boxed(
    mut v_a_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2564_: *mut LeanObject = core::ptr::null_mut();
    v_res_2564_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_();
    return v_res_2564_;
}
pub unsafe fn _init_l_String_reduceToSingleton___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v___x_2565_ = lean_box(0);
    v___x_2566_ = l_String_reduceSingleton___redArg___closed__1;
    v___x_2567_ = l_Lean_mkConst(v___x_2566_, v___x_2565_);
    return v___x_2567_;
}
pub unsafe fn l_String_reduceToSingleton___redArg(
    mut v_e_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v_val_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: u32 = 0;
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2598_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2573_ = l_String_fromExpr_x3f___redArg(v_e_2568_);
                v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
                v_isSharedCheck_2603_ = (!lean_is_exclusive(v___x_2573_)) as u8;
                if v_isSharedCheck_2603_ == 0 {
                    v___x_2576_ = v___x_2573_;
                    v_isShared_2577_ = v_isSharedCheck_2603_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2574_);
                    lean_dec(v___x_2573_);
                    v___x_2576_ = lean_box(0);
                    v_isShared_2577_ = v_isSharedCheck_2603_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2571_ = l_String_reduceAppend___redArg___closed__3;
                v___x_2572_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2572_, 0, v___x_2571_);
                return v___x_2572_;
            }
            2 => {
                if lean_obj_tag(v_a_2574_) == 1 {
                    v_val_2578_ = lean_ctor_get(v_a_2574_, 0);
                    v_isSharedCheck_2598_ = (!lean_is_exclusive(v_a_2574_)) as u8;
                    if v_isSharedCheck_2598_ == 0 {
                        v___x_2580_ = v_a_2574_;
                        v_isShared_2581_ = v_isSharedCheck_2598_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2578_);
                        lean_dec(v_a_2574_);
                        v___x_2580_ = lean_box(0);
                        v_isShared_2581_ = v_isSharedCheck_2598_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2574_);
                    v___x_2599_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2577_ == 0 {
                        lean_ctor_set(v___x_2576_, 0, v___x_2599_);
                        v___x_2601_ = v___x_2576_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
                        v___x_2601_ = v_reuseFailAlloc_2602_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2582_ = lean_string_data(v_val_2578_);
                if lean_obj_tag(v___x_2582_) == 1 {
                    v_tail_2583_ = lean_ctor_get(v___x_2582_, 1);
                    lean_inc(v_tail_2583_);
                    if lean_obj_tag(v_tail_2583_) == 0 {
                        v_head_2584_ = lean_ctor_get(v___x_2582_, 0);
                        lean_inc(v_head_2584_);
                        lean_dec_ref_known(v___x_2582_, 2);
                        v___x_2585_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_String_reduceToSingleton___redArg___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_String_reduceToSingleton___redArg___closed__0_once
                            ),
                            _init_l_String_reduceToSingleton___redArg___closed__0,
                        );
                        v___x_2586_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00String_reduceToList_spec__0___closed__3);
                        v___x_2587_ = lean_unbox_uint32(v_head_2584_);
                        lean_dec(v_head_2584_);
                        v___x_2588_ = lean_uint32_to_nat(v___x_2587_);
                        v___x_2589_ = l_Lean_mkRawNatLit(v___x_2588_);
                        v___x_2590_ = l_Lean_Expr_app___override(v___x_2586_, v___x_2589_);
                        v___x_2591_ = l_Lean_Expr_app___override(v___x_2585_, v___x_2590_);
                        if v_isShared_2581_ == 0 {
                            lean_ctor_set_tag(v___x_2580_, 0);
                            lean_ctor_set(v___x_2580_, 0, v___x_2591_);
                            v___x_2593_ = v___x_2580_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2591_);
                            v___x_2593_ = v_reuseFailAlloc_2597_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2582_, 2);
                        lean_dec(v_tail_2583_);
                        lean_del_object(v___x_2580_);
                        lean_del_object(v___x_2576_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2582_);
                    lean_del_object(v___x_2580_);
                    lean_del_object(v___x_2576_);
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v_isShared_2577_ == 0 {
                    lean_ctor_set(v___x_2576_, 0, v___x_2593_);
                    v___x_2595_ = v___x_2576_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
                    v___x_2595_ = v_reuseFailAlloc_2596_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2595_;
            }
            6 => {
                return v___x_2601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceToSingleton___redArg___boxed(
    mut v_e_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2606_: *mut LeanObject = core::ptr::null_mut();
    v_res_2606_ = l_String_reduceToSingleton___redArg(v_e_2604_);
    return v_res_2606_;
}
pub unsafe fn l_String_reduceToSingleton(
    mut v_e_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    v___x_2616_ = l_String_reduceToSingleton___redArg(v_e_2607_);
    return v___x_2616_;
}
pub unsafe fn l_String_reduceToSingleton___boxed(
    mut v_e_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
    mut v_a_2619_: *mut LeanObject,
    mut v_a_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
    mut v_a_2622_: *mut LeanObject,
    mut v_a_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2626_: *mut LeanObject = core::ptr::null_mut();
    v_res_2626_ = l_String_reduceToSingleton(
        v_e_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_,
    );
    lean_dec(v_a_2624_);
    lean_dec_ref(v_a_2623_);
    lean_dec(v_a_2622_);
    lean_dec_ref(v_a_2621_);
    lean_dec(v_a_2620_);
    lean_dec_ref(v_a_2619_);
    lean_dec(v_a_2618_);
    return v_res_2626_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_()
-> *mut LeanObject {
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    v___x_2636_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_;
    v___x_2637_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_;
    v___x_2638_ = lean_alloc_closure(
        l_String_reduceToSingleton___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2639_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_2636_, v___x_2637_, v___x_2638_);
    return v___x_2639_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12____boxed(
    mut v_a_2640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2641_: *mut LeanObject = core::ptr::null_mut();
    v_res_2641_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_();
    return v_res_2641_;
}
pub unsafe fn l_String_reduceBinPred___redArg(
    mut v_declName_2644_: *mut LeanObject,
    mut v_arity_2645_: *mut LeanObject,
    mut v_op_2646_: *mut LeanObject,
    mut v_e_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_a_2651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2653_: u8 = 0;
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v_val_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v_val_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2653_ = l_Lean_Expr_isAppOfArity(v_e_2647_, v_declName_2644_, v_arity_2645_);
                if v___x_2653_ == 0 {
                    lean_dec_ref(v_e_2647_);
                    lean_dec_ref(v_op_2646_);
                    v___x_2654_ = l_String_reduceBinPred___redArg___closed__0;
                    v___x_2655_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2655_, 0, v___x_2654_);
                    return v___x_2655_;
                } else {
                    v___x_2656_ = l_Lean_Expr_appFn_x21(v_e_2647_);
                    v___x_2657_ = l_Lean_Expr_appArg_x21(v___x_2656_);
                    lean_dec_ref(v___x_2656_);
                    v___x_2658_ = l_String_fromExpr_x3f___redArg(v___x_2657_);
                    v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
                    v_isSharedCheck_2683_ = (!lean_is_exclusive(v___x_2658_)) as u8;
                    if v_isSharedCheck_2683_ == 0 {
                        v___x_2661_ = v___x_2658_;
                        v_isShared_2662_ = v_isSharedCheck_2683_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2659_);
                        lean_dec(v___x_2658_);
                        v___x_2661_ = lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2683_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2659_) == 1 {
                    lean_del_object(v___x_2661_);
                    v_val_2663_ = lean_ctor_get(v_a_2659_, 0);
                    lean_inc(v_val_2663_);
                    lean_dec_ref_known(v_a_2659_, 1);
                    v___x_2664_ = l_Lean_Expr_appArg_x21(v_e_2647_);
                    v___x_2665_ = l_String_fromExpr_x3f___redArg(v___x_2664_);
                    v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
                    v_isSharedCheck_2678_ = (!lean_is_exclusive(v___x_2665_)) as u8;
                    if v_isSharedCheck_2678_ == 0 {
                        v___x_2668_ = v___x_2665_;
                        v_isShared_2669_ = v_isSharedCheck_2678_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2666_);
                        lean_dec(v___x_2665_);
                        v___x_2668_ = lean_box(0);
                        v_isShared_2669_ = v_isSharedCheck_2678_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2659_);
                    lean_dec_ref(v_e_2647_);
                    lean_dec_ref(v_op_2646_);
                    v___x_2679_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_2662_ == 0 {
                        lean_ctor_set(v___x_2661_, 0, v___x_2679_);
                        v___x_2681_ = v___x_2661_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
                        v___x_2681_ = v_reuseFailAlloc_2682_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2666_) == 1 {
                    lean_del_object(v___x_2668_);
                    v_val_2670_ = lean_ctor_get(v_a_2666_, 0);
                    lean_inc(v_val_2670_);
                    lean_dec_ref_known(v_a_2666_, 1);
                    v___x_2671_ = lean_apply_2(v_op_2646_, v_val_2663_, v_val_2670_);
                    v___x_2672_ = (lean_unbox(v___x_2671_) as u8);
                    v___x_2673_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_2647_,
                        v___x_2672_,
                        v_a_2648_,
                        v_a_2649_,
                        v_a_2650_,
                        v_a_2651_,
                    );
                    return v___x_2673_;
                } else {
                    lean_dec(v_a_2666_);
                    lean_dec(v_val_2663_);
                    lean_dec_ref(v_e_2647_);
                    lean_dec_ref(v_op_2646_);
                    v___x_2674_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_2669_ == 0 {
                        lean_ctor_set(v___x_2668_, 0, v___x_2674_);
                        v___x_2676_ = v___x_2668_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
                        v___x_2676_ = v_reuseFailAlloc_2677_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2676_;
            }
            4 => {
                return v___x_2681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceBinPred___redArg___boxed(
    mut v_declName_2684_: *mut LeanObject,
    mut v_arity_2685_: *mut LeanObject,
    mut v_op_2686_: *mut LeanObject,
    mut v_e_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
    mut v_a_2689_: *mut LeanObject,
    mut v_a_2690_: *mut LeanObject,
    mut v_a_2691_: *mut LeanObject,
    mut v_a_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2693_: *mut LeanObject = core::ptr::null_mut();
    v_res_2693_ = l_String_reduceBinPred___redArg(
        v_declName_2684_,
        v_arity_2685_,
        v_op_2686_,
        v_e_2687_,
        v_a_2688_,
        v_a_2689_,
        v_a_2690_,
        v_a_2691_,
    );
    lean_dec(v_a_2691_);
    lean_dec_ref(v_a_2690_);
    lean_dec(v_a_2689_);
    lean_dec_ref(v_a_2688_);
    lean_dec(v_declName_2684_);
    return v_res_2693_;
}
pub unsafe fn l_String_reduceBinPred(
    mut v_declName_2694_: *mut LeanObject,
    mut v_arity_2695_: *mut LeanObject,
    mut v_op_2696_: *mut LeanObject,
    mut v_e_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
    mut v_a_2700_: *mut LeanObject,
    mut v_a_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
    mut v_a_2703_: *mut LeanObject,
    mut v_a_2704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2706_: u8 = 0;
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v_val_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v_val_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: u8 = 0;
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2706_ = l_Lean_Expr_isAppOfArity(v_e_2697_, v_declName_2694_, v_arity_2695_);
                if v___x_2706_ == 0 {
                    lean_dec_ref(v_e_2697_);
                    lean_dec_ref(v_op_2696_);
                    v___x_2707_ = l_String_reduceBinPred___redArg___closed__0;
                    v___x_2708_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2708_, 0, v___x_2707_);
                    return v___x_2708_;
                } else {
                    v___x_2709_ = l_Lean_Expr_appFn_x21(v_e_2697_);
                    v___x_2710_ = l_Lean_Expr_appArg_x21(v___x_2709_);
                    lean_dec_ref(v___x_2709_);
                    v___x_2711_ = l_String_fromExpr_x3f___redArg(v___x_2710_);
                    v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
                    v_isSharedCheck_2736_ = (!lean_is_exclusive(v___x_2711_)) as u8;
                    if v_isSharedCheck_2736_ == 0 {
                        v___x_2714_ = v___x_2711_;
                        v_isShared_2715_ = v_isSharedCheck_2736_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2712_);
                        lean_dec(v___x_2711_);
                        v___x_2714_ = lean_box(0);
                        v_isShared_2715_ = v_isSharedCheck_2736_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2712_) == 1 {
                    lean_del_object(v___x_2714_);
                    v_val_2716_ = lean_ctor_get(v_a_2712_, 0);
                    lean_inc(v_val_2716_);
                    lean_dec_ref_known(v_a_2712_, 1);
                    v___x_2717_ = l_Lean_Expr_appArg_x21(v_e_2697_);
                    v___x_2718_ = l_String_fromExpr_x3f___redArg(v___x_2717_);
                    v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
                    v_isSharedCheck_2731_ = (!lean_is_exclusive(v___x_2718_)) as u8;
                    if v_isSharedCheck_2731_ == 0 {
                        v___x_2721_ = v___x_2718_;
                        v_isShared_2722_ = v_isSharedCheck_2731_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2719_);
                        lean_dec(v___x_2718_);
                        v___x_2721_ = lean_box(0);
                        v_isShared_2722_ = v_isSharedCheck_2731_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2712_);
                    lean_dec_ref(v_e_2697_);
                    lean_dec_ref(v_op_2696_);
                    v___x_2732_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_2715_ == 0 {
                        lean_ctor_set(v___x_2714_, 0, v___x_2732_);
                        v___x_2734_ = v___x_2714_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
                        v___x_2734_ = v_reuseFailAlloc_2735_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2719_) == 1 {
                    lean_del_object(v___x_2721_);
                    v_val_2723_ = lean_ctor_get(v_a_2719_, 0);
                    lean_inc(v_val_2723_);
                    lean_dec_ref_known(v_a_2719_, 1);
                    v___x_2724_ = lean_apply_2(v_op_2696_, v_val_2716_, v_val_2723_);
                    v___x_2725_ = (lean_unbox(v___x_2724_) as u8);
                    v___x_2726_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_2697_,
                        v___x_2725_,
                        v_a_2701_,
                        v_a_2702_,
                        v_a_2703_,
                        v_a_2704_,
                    );
                    return v___x_2726_;
                } else {
                    lean_dec(v_a_2719_);
                    lean_dec(v_val_2716_);
                    lean_dec_ref(v_e_2697_);
                    lean_dec_ref(v_op_2696_);
                    v___x_2727_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_2722_ == 0 {
                        lean_ctor_set(v___x_2721_, 0, v___x_2727_);
                        v___x_2729_ = v___x_2721_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
                        v___x_2729_ = v_reuseFailAlloc_2730_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2729_;
            }
            4 => {
                return v___x_2734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceBinPred___boxed(
    mut v_declName_2737_: *mut LeanObject,
    mut v_arity_2738_: *mut LeanObject,
    mut v_op_2739_: *mut LeanObject,
    mut v_e_2740_: *mut LeanObject,
    mut v_a_2741_: *mut LeanObject,
    mut v_a_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
    mut v_a_2744_: *mut LeanObject,
    mut v_a_2745_: *mut LeanObject,
    mut v_a_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
    mut v_a_2748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2749_: *mut LeanObject = core::ptr::null_mut();
    v_res_2749_ = l_String_reduceBinPred(
        v_declName_2737_,
        v_arity_2738_,
        v_op_2739_,
        v_e_2740_,
        v_a_2741_,
        v_a_2742_,
        v_a_2743_,
        v_a_2744_,
        v_a_2745_,
        v_a_2746_,
        v_a_2747_,
    );
    lean_dec(v_a_2747_);
    lean_dec_ref(v_a_2746_);
    lean_dec(v_a_2745_);
    lean_dec_ref(v_a_2744_);
    lean_dec(v_a_2743_);
    lean_dec_ref(v_a_2742_);
    lean_dec(v_a_2741_);
    lean_dec(v_declName_2737_);
    return v_res_2749_;
}
pub unsafe fn _init_l_String_reduceBoolPred___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    v___x_2755_ = lean_box(0);
    v___x_2756_ = l_String_reduceBoolPred___redArg___closed__2;
    v___x_2757_ = l_Lean_mkConst(v___x_2756_, v___x_2755_);
    return v___x_2757_;
}
pub unsafe fn _init_l_String_reduceBoolPred___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    v___x_2762_ = lean_box(0);
    v___x_2763_ = l_String_reduceBoolPred___redArg___closed__5;
    v___x_2764_ = l_Lean_mkConst(v___x_2763_, v___x_2762_);
    return v___x_2764_;
}
pub unsafe fn l_String_reduceBoolPred___redArg(
    mut v_declName_2765_: *mut LeanObject,
    mut v_arity_2766_: *mut LeanObject,
    mut v_op_2767_: *mut LeanObject,
    mut v_e_2768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2770_: u8 = 0;
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v_val_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2783_: u8 = 0;
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v___y_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_isSharedCheck_2808_: u8 = 0;
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2770_ = l_Lean_Expr_isAppOfArity(v_e_2768_, v_declName_2765_, v_arity_2766_);
                if v___x_2770_ == 0 {
                    lean_dec_ref(v_op_2767_);
                    v___x_2771_ = l_String_reduceAppend___redArg___closed__3;
                    v___x_2772_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2772_, 0, v___x_2771_);
                    return v___x_2772_;
                } else {
                    v___x_2773_ = l_Lean_Expr_appFn_x21(v_e_2768_);
                    v___x_2774_ = l_Lean_Expr_appArg_x21(v___x_2773_);
                    lean_dec_ref(v___x_2773_);
                    v___x_2775_ = l_String_fromExpr_x3f___redArg(v___x_2774_);
                    v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
                    v_isSharedCheck_2813_ = (!lean_is_exclusive(v___x_2775_)) as u8;
                    if v_isSharedCheck_2813_ == 0 {
                        v___x_2778_ = v___x_2775_;
                        v_isShared_2779_ = v_isSharedCheck_2813_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2776_);
                        lean_dec(v___x_2775_);
                        v___x_2778_ = lean_box(0);
                        v_isShared_2779_ = v_isSharedCheck_2813_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2776_) == 1 {
                    v_val_2780_ = lean_ctor_get(v_a_2776_, 0);
                    v_isSharedCheck_2808_ = (!lean_is_exclusive(v_a_2776_)) as u8;
                    if v_isSharedCheck_2808_ == 0 {
                        v___x_2782_ = v_a_2776_;
                        v_isShared_2783_ = v_isSharedCheck_2808_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2780_);
                        lean_dec(v_a_2776_);
                        v___x_2782_ = lean_box(0);
                        v_isShared_2783_ = v_isSharedCheck_2808_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2776_);
                    lean_dec_ref(v_op_2767_);
                    v___x_2809_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2779_ == 0 {
                        lean_ctor_set(v___x_2778_, 0, v___x_2809_);
                        v___x_2811_ = v___x_2778_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
                        v___x_2811_ = v_reuseFailAlloc_2812_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2784_ = l_Lean_Expr_appArg_x21(v_e_2768_);
                v___x_2785_ = l_String_fromExpr_x3f___redArg(v___x_2784_);
                v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
                v_isSharedCheck_2807_ = (!lean_is_exclusive(v___x_2785_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v___x_2788_ = v___x_2785_;
                    v_isShared_2789_ = v_isSharedCheck_2807_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_2786_);
                    lean_dec(v___x_2785_);
                    v___x_2788_ = lean_box(0);
                    v_isShared_2789_ = v_isSharedCheck_2807_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_a_2786_) == 1 {
                    lean_del_object(v___x_2778_);
                    v_val_2798_ = lean_ctor_get(v_a_2786_, 0);
                    lean_inc(v_val_2798_);
                    lean_dec_ref_known(v_a_2786_, 1);
                    v___x_2799_ = lean_apply_2(v_op_2767_, v_val_2780_, v_val_2798_);
                    v___x_2800_ = (lean_unbox(v___x_2799_) as u8);
                    if v___x_2800_ == 0 {
                        v___x_2801_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_String_reduceBoolPred___redArg___closed__3),
                            core::ptr::addr_of_mut!(
                                l_String_reduceBoolPred___redArg___closed__3_once
                            ),
                            _init_l_String_reduceBoolPred___redArg___closed__3,
                        );
                        v___y_2791_ = v___x_2801_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2802_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_String_reduceBoolPred___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_String_reduceBoolPred___redArg___closed__6_once
                            ),
                            _init_l_String_reduceBoolPred___redArg___closed__6,
                        );
                        v___y_2791_ = v___x_2802_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2788_);
                    lean_dec(v_a_2786_);
                    lean_del_object(v___x_2782_);
                    lean_dec(v_val_2780_);
                    lean_dec_ref(v_op_2767_);
                    v___x_2803_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2779_ == 0 {
                        lean_ctor_set(v___x_2778_, 0, v___x_2803_);
                        v___x_2805_ = v___x_2778_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
                        v___x_2805_ = v_reuseFailAlloc_2806_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                lean_inc_ref(v___y_2791_);
                if v_isShared_2783_ == 0 {
                    lean_ctor_set_tag(v___x_2782_, 0);
                    lean_ctor_set(v___x_2782_, 0, v___y_2791_);
                    v___x_2793_ = v___x_2782_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___y_2791_);
                    v___x_2793_ = v_reuseFailAlloc_2797_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2789_ == 0 {
                    lean_ctor_set(v___x_2788_, 0, v___x_2793_);
                    v___x_2795_ = v___x_2788_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
                    v___x_2795_ = v_reuseFailAlloc_2796_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2795_;
            }
            7 => {
                return v___x_2805_;
            }
            8 => {
                return v___x_2811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceBoolPred___redArg___boxed(
    mut v_declName_2814_: *mut LeanObject,
    mut v_arity_2815_: *mut LeanObject,
    mut v_op_2816_: *mut LeanObject,
    mut v_e_2817_: *mut LeanObject,
    mut v_a_2818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2819_: *mut LeanObject = core::ptr::null_mut();
    v_res_2819_ =
        l_String_reduceBoolPred___redArg(v_declName_2814_, v_arity_2815_, v_op_2816_, v_e_2817_);
    lean_dec_ref(v_e_2817_);
    lean_dec(v_declName_2814_);
    return v_res_2819_;
}
pub unsafe fn l_String_reduceBoolPred(
    mut v_declName_2820_: *mut LeanObject,
    mut v_arity_2821_: *mut LeanObject,
    mut v_op_2822_: *mut LeanObject,
    mut v_e_2823_: *mut LeanObject,
    mut v_a_2824_: *mut LeanObject,
    mut v_a_2825_: *mut LeanObject,
    mut v_a_2826_: *mut LeanObject,
    mut v_a_2827_: *mut LeanObject,
    mut v_a_2828_: *mut LeanObject,
    mut v_a_2829_: *mut LeanObject,
    mut v_a_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2832_: u8 = 0;
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2841_: u8 = 0;
    let mut v_val_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v___y_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2832_ = l_Lean_Expr_isAppOfArity(v_e_2823_, v_declName_2820_, v_arity_2821_);
                if v___x_2832_ == 0 {
                    lean_dec_ref(v_op_2822_);
                    v___x_2833_ = l_String_reduceAppend___redArg___closed__3;
                    v___x_2834_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2834_, 0, v___x_2833_);
                    return v___x_2834_;
                } else {
                    v___x_2835_ = l_Lean_Expr_appFn_x21(v_e_2823_);
                    v___x_2836_ = l_Lean_Expr_appArg_x21(v___x_2835_);
                    lean_dec_ref(v___x_2835_);
                    v___x_2837_ = l_String_fromExpr_x3f___redArg(v___x_2836_);
                    v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
                    v_isSharedCheck_2875_ = (!lean_is_exclusive(v___x_2837_)) as u8;
                    if v_isSharedCheck_2875_ == 0 {
                        v___x_2840_ = v___x_2837_;
                        v_isShared_2841_ = v_isSharedCheck_2875_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2838_);
                        lean_dec(v___x_2837_);
                        v___x_2840_ = lean_box(0);
                        v_isShared_2841_ = v_isSharedCheck_2875_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2838_) == 1 {
                    v_val_2842_ = lean_ctor_get(v_a_2838_, 0);
                    v_isSharedCheck_2870_ = (!lean_is_exclusive(v_a_2838_)) as u8;
                    if v_isSharedCheck_2870_ == 0 {
                        v___x_2844_ = v_a_2838_;
                        v_isShared_2845_ = v_isSharedCheck_2870_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2842_);
                        lean_dec(v_a_2838_);
                        v___x_2844_ = lean_box(0);
                        v_isShared_2845_ = v_isSharedCheck_2870_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2838_);
                    lean_dec_ref(v_op_2822_);
                    v___x_2871_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2841_ == 0 {
                        lean_ctor_set(v___x_2840_, 0, v___x_2871_);
                        v___x_2873_ = v___x_2840_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
                        v___x_2873_ = v_reuseFailAlloc_2874_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2846_ = l_Lean_Expr_appArg_x21(v_e_2823_);
                v___x_2847_ = l_String_fromExpr_x3f___redArg(v___x_2846_);
                v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
                v_isSharedCheck_2869_ = (!lean_is_exclusive(v___x_2847_)) as u8;
                if v_isSharedCheck_2869_ == 0 {
                    v___x_2850_ = v___x_2847_;
                    v_isShared_2851_ = v_isSharedCheck_2869_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_2848_);
                    lean_dec(v___x_2847_);
                    v___x_2850_ = lean_box(0);
                    v_isShared_2851_ = v_isSharedCheck_2869_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_a_2848_) == 1 {
                    lean_del_object(v___x_2840_);
                    v_val_2860_ = lean_ctor_get(v_a_2848_, 0);
                    lean_inc(v_val_2860_);
                    lean_dec_ref_known(v_a_2848_, 1);
                    v___x_2861_ = lean_apply_2(v_op_2822_, v_val_2842_, v_val_2860_);
                    v___x_2862_ = (lean_unbox(v___x_2861_) as u8);
                    if v___x_2862_ == 0 {
                        v___x_2863_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_String_reduceBoolPred___redArg___closed__3),
                            core::ptr::addr_of_mut!(
                                l_String_reduceBoolPred___redArg___closed__3_once
                            ),
                            _init_l_String_reduceBoolPred___redArg___closed__3,
                        );
                        v___y_2853_ = v___x_2863_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2864_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_String_reduceBoolPred___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_String_reduceBoolPred___redArg___closed__6_once
                            ),
                            _init_l_String_reduceBoolPred___redArg___closed__6,
                        );
                        v___y_2853_ = v___x_2864_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2850_);
                    lean_dec(v_a_2848_);
                    lean_del_object(v___x_2844_);
                    lean_dec(v_val_2842_);
                    lean_dec_ref(v_op_2822_);
                    v___x_2865_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_2841_ == 0 {
                        lean_ctor_set(v___x_2840_, 0, v___x_2865_);
                        v___x_2867_ = v___x_2840_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
                        v___x_2867_ = v_reuseFailAlloc_2868_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                lean_inc_ref(v___y_2853_);
                if v_isShared_2845_ == 0 {
                    lean_ctor_set_tag(v___x_2844_, 0);
                    lean_ctor_set(v___x_2844_, 0, v___y_2853_);
                    v___x_2855_ = v___x_2844_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___y_2853_);
                    v___x_2855_ = v_reuseFailAlloc_2859_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2851_ == 0 {
                    lean_ctor_set(v___x_2850_, 0, v___x_2855_);
                    v___x_2857_ = v___x_2850_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
                    v___x_2857_ = v_reuseFailAlloc_2858_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2857_;
            }
            7 => {
                return v___x_2867_;
            }
            8 => {
                return v___x_2873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceBoolPred___boxed(
    mut v_declName_2876_: *mut LeanObject,
    mut v_arity_2877_: *mut LeanObject,
    mut v_op_2878_: *mut LeanObject,
    mut v_e_2879_: *mut LeanObject,
    mut v_a_2880_: *mut LeanObject,
    mut v_a_2881_: *mut LeanObject,
    mut v_a_2882_: *mut LeanObject,
    mut v_a_2883_: *mut LeanObject,
    mut v_a_2884_: *mut LeanObject,
    mut v_a_2885_: *mut LeanObject,
    mut v_a_2886_: *mut LeanObject,
    mut v_a_2887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2888_: *mut LeanObject = core::ptr::null_mut();
    v_res_2888_ = l_String_reduceBoolPred(
        v_declName_2876_,
        v_arity_2877_,
        v_op_2878_,
        v_e_2879_,
        v_a_2880_,
        v_a_2881_,
        v_a_2882_,
        v_a_2883_,
        v_a_2884_,
        v_a_2885_,
        v_a_2886_,
    );
    lean_dec(v_a_2886_);
    lean_dec_ref(v_a_2885_);
    lean_dec(v_a_2884_);
    lean_dec_ref(v_a_2883_);
    lean_dec(v_a_2882_);
    lean_dec_ref(v_a_2881_);
    lean_dec(v_a_2880_);
    lean_dec_ref(v_e_2879_);
    lean_dec(v_declName_2876_);
    return v_res_2888_;
}
pub unsafe fn l_String_reduceLT___redArg(
    mut v_e_2894_: *mut LeanObject,
    mut v_a_2895_: *mut LeanObject,
    mut v_a_2896_: *mut LeanObject,
    mut v_a_2897_: *mut LeanObject,
    mut v_a_2898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v_val_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v_val_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2900_ = l_String_reduceLT___redArg___closed__2;
                v___x_2901_ = lean_unsigned_to_nat(4);
                v___x_2902_ = l_Lean_Expr_isAppOfArity(v_e_2894_, v___x_2900_, v___x_2901_);
                if v___x_2902_ == 0 {
                    lean_dec_ref(v_e_2894_);
                    v___x_2903_ = l_String_reduceBinPred___redArg___closed__0;
                    v___x_2904_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2904_, 0, v___x_2903_);
                    return v___x_2904_;
                } else {
                    v___x_2905_ = l_Lean_Expr_appFn_x21(v_e_2894_);
                    v___x_2906_ = l_Lean_Expr_appArg_x21(v___x_2905_);
                    lean_dec_ref(v___x_2905_);
                    v___x_2907_ = l_String_fromExpr_x3f___redArg(v___x_2906_);
                    v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
                    v_isSharedCheck_2931_ = (!lean_is_exclusive(v___x_2907_)) as u8;
                    if v_isSharedCheck_2931_ == 0 {
                        v___x_2910_ = v___x_2907_;
                        v_isShared_2911_ = v_isSharedCheck_2931_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2908_);
                        lean_dec(v___x_2907_);
                        v___x_2910_ = lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_2931_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2908_) == 1 {
                    lean_del_object(v___x_2910_);
                    v_val_2912_ = lean_ctor_get(v_a_2908_, 0);
                    lean_inc(v_val_2912_);
                    lean_dec_ref_known(v_a_2908_, 1);
                    v___x_2913_ = l_Lean_Expr_appArg_x21(v_e_2894_);
                    v___x_2914_ = l_String_fromExpr_x3f___redArg(v___x_2913_);
                    v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
                    v_isSharedCheck_2926_ = (!lean_is_exclusive(v___x_2914_)) as u8;
                    if v_isSharedCheck_2926_ == 0 {
                        v___x_2917_ = v___x_2914_;
                        v_isShared_2918_ = v_isSharedCheck_2926_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2915_);
                        lean_dec(v___x_2914_);
                        v___x_2917_ = lean_box(0);
                        v_isShared_2918_ = v_isSharedCheck_2926_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2908_);
                    lean_dec_ref(v_e_2894_);
                    v___x_2927_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_2911_ == 0 {
                        lean_ctor_set(v___x_2910_, 0, v___x_2927_);
                        v___x_2929_ = v___x_2910_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
                        v___x_2929_ = v_reuseFailAlloc_2930_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2915_) == 1 {
                    lean_del_object(v___x_2917_);
                    v_val_2919_ = lean_ctor_get(v_a_2915_, 0);
                    lean_inc(v_val_2919_);
                    lean_dec_ref_known(v_a_2915_, 1);
                    v___x_2920_ = lean_string_dec_lt(v_val_2912_, v_val_2919_);
                    lean_dec(v_val_2919_);
                    lean_dec(v_val_2912_);
                    v___x_2921_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_2894_,
                        v___x_2920_,
                        v_a_2895_,
                        v_a_2896_,
                        v_a_2897_,
                        v_a_2898_,
                    );
                    return v___x_2921_;
                } else {
                    lean_dec(v_a_2915_);
                    lean_dec(v_val_2912_);
                    lean_dec_ref(v_e_2894_);
                    v___x_2922_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_2918_ == 0 {
                        lean_ctor_set(v___x_2917_, 0, v___x_2922_);
                        v___x_2924_ = v___x_2917_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
                        v___x_2924_ = v_reuseFailAlloc_2925_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2924_;
            }
            4 => {
                return v___x_2929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceLT___redArg___boxed(
    mut v_e_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
    mut v_a_2934_: *mut LeanObject,
    mut v_a_2935_: *mut LeanObject,
    mut v_a_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2938_: *mut LeanObject = core::ptr::null_mut();
    v_res_2938_ = l_String_reduceLT___redArg(v_e_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
    lean_dec(v_a_2936_);
    lean_dec_ref(v_a_2935_);
    lean_dec(v_a_2934_);
    lean_dec_ref(v_a_2933_);
    return v_res_2938_;
}
pub unsafe fn l_String_reduceLT(
    mut v_e_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
    mut v_a_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v_a_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
    mut v_a_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    v___x_2948_ = l_String_reduceLT___redArg(v_e_2939_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
    return v___x_2948_;
}
pub unsafe fn l_String_reduceLT___boxed(
    mut v_e_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
    mut v_a_2951_: *mut LeanObject,
    mut v_a_2952_: *mut LeanObject,
    mut v_a_2953_: *mut LeanObject,
    mut v_a_2954_: *mut LeanObject,
    mut v_a_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2958_: *mut LeanObject = core::ptr::null_mut();
    v_res_2958_ = l_String_reduceLT(
        v_e_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_,
    );
    lean_dec(v_a_2956_);
    lean_dec_ref(v_a_2955_);
    lean_dec(v_a_2954_);
    lean_dec_ref(v_a_2953_);
    lean_dec(v_a_2952_);
    lean_dec_ref(v_a_2951_);
    lean_dec(v_a_2950_);
    return v_res_2958_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    v___x_2977_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_;
    v___x_2978_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_;
    v___x_2979_ = lean_alloc_closure(l_String_reduceLT___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_2980_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2977_, v___x_2978_, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20____boxed(
    mut v_a_2981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2982_: *mut LeanObject = core::ptr::null_mut();
    v_res_2982_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_();
    return v_res_2982_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    v___x_2983_ = lean_alloc_closure(l_String_reduceLT___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_2984_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2984_, 0, v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    v___x_2986_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_;
    v___x_2987_ = 1;
    v___x_2988_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_);
    v___x_2989_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_2986_, v___x_2987_, v___x_2988_);
    return v___x_2989_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22____boxed(
    mut v_a_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2991_: *mut LeanObject = core::ptr::null_mut();
    v_res_2991_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_();
    return v_res_2991_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    v___x_2993_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_;
    v___x_2994_ = 1;
    v___x_2995_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_);
    v___x_2996_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_2993_, v___x_2994_, v___x_2995_);
    return v___x_2996_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24____boxed(
    mut v_a_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2998_: *mut LeanObject = core::ptr::null_mut();
    v_res_2998_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_();
    return v_res_2998_;
}
pub unsafe fn l_String_reduceLE___redArg(
    mut v_e_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
    mut v_a_3006_: *mut LeanObject,
    mut v_a_3007_: *mut LeanObject,
    mut v_a_3008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3021_: u8 = 0;
    let mut v_val_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3028_: u8 = 0;
    let mut v_val_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: u8 = 0;
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3010_ = l_String_reduceLE___redArg___closed__2;
                v___x_3011_ = lean_unsigned_to_nat(4);
                v___x_3012_ = l_Lean_Expr_isAppOfArity(v_e_3004_, v___x_3010_, v___x_3011_);
                if v___x_3012_ == 0 {
                    lean_dec_ref(v_e_3004_);
                    v___x_3013_ = l_String_reduceBinPred___redArg___closed__0;
                    v___x_3014_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3014_, 0, v___x_3013_);
                    return v___x_3014_;
                } else {
                    v___x_3015_ = l_Lean_Expr_appFn_x21(v_e_3004_);
                    v___x_3016_ = l_Lean_Expr_appArg_x21(v___x_3015_);
                    lean_dec_ref(v___x_3015_);
                    v___x_3017_ = l_String_fromExpr_x3f___redArg(v___x_3016_);
                    v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
                    v_isSharedCheck_3041_ = (!lean_is_exclusive(v___x_3017_)) as u8;
                    if v_isSharedCheck_3041_ == 0 {
                        v___x_3020_ = v___x_3017_;
                        v_isShared_3021_ = v_isSharedCheck_3041_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3018_);
                        lean_dec(v___x_3017_);
                        v___x_3020_ = lean_box(0);
                        v_isShared_3021_ = v_isSharedCheck_3041_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3018_) == 1 {
                    lean_del_object(v___x_3020_);
                    v_val_3022_ = lean_ctor_get(v_a_3018_, 0);
                    lean_inc(v_val_3022_);
                    lean_dec_ref_known(v_a_3018_, 1);
                    v___x_3023_ = l_Lean_Expr_appArg_x21(v_e_3004_);
                    v___x_3024_ = l_String_fromExpr_x3f___redArg(v___x_3023_);
                    v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
                    v_isSharedCheck_3036_ = (!lean_is_exclusive(v___x_3024_)) as u8;
                    if v_isSharedCheck_3036_ == 0 {
                        v___x_3027_ = v___x_3024_;
                        v_isShared_3028_ = v_isSharedCheck_3036_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3025_);
                        lean_dec(v___x_3024_);
                        v___x_3027_ = lean_box(0);
                        v_isShared_3028_ = v_isSharedCheck_3036_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3018_);
                    lean_dec_ref(v_e_3004_);
                    v___x_3037_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3021_ == 0 {
                        lean_ctor_set(v___x_3020_, 0, v___x_3037_);
                        v___x_3039_ = v___x_3020_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
                        v___x_3039_ = v_reuseFailAlloc_3040_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3025_) == 1 {
                    lean_del_object(v___x_3027_);
                    v_val_3029_ = lean_ctor_get(v_a_3025_, 0);
                    lean_inc(v_val_3029_);
                    lean_dec_ref_known(v_a_3025_, 1);
                    v___x_3030_ = l_String_decLE(v_val_3022_, v_val_3029_);
                    lean_dec(v_val_3029_);
                    lean_dec(v_val_3022_);
                    v___x_3031_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_3004_,
                        v___x_3030_,
                        v_a_3005_,
                        v_a_3006_,
                        v_a_3007_,
                        v_a_3008_,
                    );
                    return v___x_3031_;
                } else {
                    lean_dec(v_a_3025_);
                    lean_dec(v_val_3022_);
                    lean_dec_ref(v_e_3004_);
                    v___x_3032_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3028_ == 0 {
                        lean_ctor_set(v___x_3027_, 0, v___x_3032_);
                        v___x_3034_ = v___x_3027_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
                        v___x_3034_ = v_reuseFailAlloc_3035_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3034_;
            }
            4 => {
                return v___x_3039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceLE___redArg___boxed(
    mut v_e_3042_: *mut LeanObject,
    mut v_a_3043_: *mut LeanObject,
    mut v_a_3044_: *mut LeanObject,
    mut v_a_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
    mut v_a_3047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3048_: *mut LeanObject = core::ptr::null_mut();
    v_res_3048_ = l_String_reduceLE___redArg(v_e_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_);
    lean_dec(v_a_3046_);
    lean_dec_ref(v_a_3045_);
    lean_dec(v_a_3044_);
    lean_dec_ref(v_a_3043_);
    return v_res_3048_;
}
pub unsafe fn l_String_reduceLE(
    mut v_e_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
    mut v_a_3052_: *mut LeanObject,
    mut v_a_3053_: *mut LeanObject,
    mut v_a_3054_: *mut LeanObject,
    mut v_a_3055_: *mut LeanObject,
    mut v_a_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    v___x_3058_ = l_String_reduceLE___redArg(v_e_3049_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
    return v___x_3058_;
}
pub unsafe fn l_String_reduceLE___boxed(
    mut v_e_3059_: *mut LeanObject,
    mut v_a_3060_: *mut LeanObject,
    mut v_a_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
    mut v_a_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3068_: *mut LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_String_reduceLE(
        v_e_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_,
    );
    lean_dec(v_a_3066_);
    lean_dec_ref(v_a_3065_);
    lean_dec(v_a_3064_);
    lean_dec_ref(v_a_3063_);
    lean_dec(v_a_3062_);
    lean_dec_ref(v_a_3061_);
    lean_dec(v_a_3060_);
    return v_res_3068_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    v___x_3087_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_;
    v___x_3088_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_;
    v___x_3089_ = lean_alloc_closure(l_String_reduceLE___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3090_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3087_, v___x_3088_, v___x_3089_);
    return v___x_3090_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20____boxed(
    mut v_a_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3092_: *mut LeanObject = core::ptr::null_mut();
    v_res_3092_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_();
    return v_res_3092_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = lean_alloc_closure(l_String_reduceLE___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3094_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3094_, 0, v___x_3093_);
    return v___x_3094_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    v___x_3096_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_;
    v___x_3097_ = 1;
    v___x_3098_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_);
    v___x_3099_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3096_, v___x_3097_, v___x_3098_);
    return v___x_3099_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22____boxed(
    mut v_a_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3101_: *mut LeanObject = core::ptr::null_mut();
    v_res_3101_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_();
    return v_res_3101_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    v___x_3103_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_;
    v___x_3104_ = 1;
    v___x_3105_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_);
    v___x_3106_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3103_, v___x_3104_, v___x_3105_);
    return v___x_3106_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24____boxed(
    mut v_a_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3108_: *mut LeanObject = core::ptr::null_mut();
    v_res_3108_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_();
    return v_res_3108_;
}
pub unsafe fn l_String_reduceGT___redArg(
    mut v_e_3114_: *mut LeanObject,
    mut v_a_3115_: *mut LeanObject,
    mut v_a_3116_: *mut LeanObject,
    mut v_a_3117_: *mut LeanObject,
    mut v_a_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v_val_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v_val_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3146_: u8 = 0;
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3120_ = l_String_reduceGT___redArg___closed__2;
                v___x_3121_ = lean_unsigned_to_nat(4);
                v___x_3122_ = l_Lean_Expr_isAppOfArity(v_e_3114_, v___x_3120_, v___x_3121_);
                if v___x_3122_ == 0 {
                    lean_dec_ref(v_e_3114_);
                    v___x_3123_ = l_String_reduceBinPred___redArg___closed__0;
                    v___x_3124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3124_, 0, v___x_3123_);
                    return v___x_3124_;
                } else {
                    v___x_3125_ = l_Lean_Expr_appFn_x21(v_e_3114_);
                    v___x_3126_ = l_Lean_Expr_appArg_x21(v___x_3125_);
                    lean_dec_ref(v___x_3125_);
                    v___x_3127_ = l_String_fromExpr_x3f___redArg(v___x_3126_);
                    v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
                    v_isSharedCheck_3151_ = (!lean_is_exclusive(v___x_3127_)) as u8;
                    if v_isSharedCheck_3151_ == 0 {
                        v___x_3130_ = v___x_3127_;
                        v_isShared_3131_ = v_isSharedCheck_3151_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3128_);
                        lean_dec(v___x_3127_);
                        v___x_3130_ = lean_box(0);
                        v_isShared_3131_ = v_isSharedCheck_3151_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3128_) == 1 {
                    lean_del_object(v___x_3130_);
                    v_val_3132_ = lean_ctor_get(v_a_3128_, 0);
                    lean_inc(v_val_3132_);
                    lean_dec_ref_known(v_a_3128_, 1);
                    v___x_3133_ = l_Lean_Expr_appArg_x21(v_e_3114_);
                    v___x_3134_ = l_String_fromExpr_x3f___redArg(v___x_3133_);
                    v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
                    v_isSharedCheck_3146_ = (!lean_is_exclusive(v___x_3134_)) as u8;
                    if v_isSharedCheck_3146_ == 0 {
                        v___x_3137_ = v___x_3134_;
                        v_isShared_3138_ = v_isSharedCheck_3146_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3135_);
                        lean_dec(v___x_3134_);
                        v___x_3137_ = lean_box(0);
                        v_isShared_3138_ = v_isSharedCheck_3146_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3128_);
                    lean_dec_ref(v_e_3114_);
                    v___x_3147_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3131_ == 0 {
                        lean_ctor_set(v___x_3130_, 0, v___x_3147_);
                        v___x_3149_ = v___x_3130_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
                        v___x_3149_ = v_reuseFailAlloc_3150_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3135_) == 1 {
                    lean_del_object(v___x_3137_);
                    v_val_3139_ = lean_ctor_get(v_a_3135_, 0);
                    lean_inc(v_val_3139_);
                    lean_dec_ref_known(v_a_3135_, 1);
                    v___x_3140_ = lean_string_dec_lt(v_val_3139_, v_val_3132_);
                    lean_dec(v_val_3132_);
                    lean_dec(v_val_3139_);
                    v___x_3141_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_3114_,
                        v___x_3140_,
                        v_a_3115_,
                        v_a_3116_,
                        v_a_3117_,
                        v_a_3118_,
                    );
                    return v___x_3141_;
                } else {
                    lean_dec(v_a_3135_);
                    lean_dec(v_val_3132_);
                    lean_dec_ref(v_e_3114_);
                    v___x_3142_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3138_ == 0 {
                        lean_ctor_set(v___x_3137_, 0, v___x_3142_);
                        v___x_3144_ = v___x_3137_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
                        v___x_3144_ = v_reuseFailAlloc_3145_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3144_;
            }
            4 => {
                return v___x_3149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceGT___redArg___boxed(
    mut v_e_3152_: *mut LeanObject,
    mut v_a_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
    mut v_a_3155_: *mut LeanObject,
    mut v_a_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3158_: *mut LeanObject = core::ptr::null_mut();
    v_res_3158_ = l_String_reduceGT___redArg(v_e_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_);
    lean_dec(v_a_3156_);
    lean_dec_ref(v_a_3155_);
    lean_dec(v_a_3154_);
    lean_dec_ref(v_a_3153_);
    return v_res_3158_;
}
pub unsafe fn l_String_reduceGT(
    mut v_e_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_a_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
    mut v_a_3164_: *mut LeanObject,
    mut v_a_3165_: *mut LeanObject,
    mut v_a_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_String_reduceGT___redArg(v_e_3159_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
    return v___x_3168_;
}
pub unsafe fn l_String_reduceGT___boxed(
    mut v_e_3169_: *mut LeanObject,
    mut v_a_3170_: *mut LeanObject,
    mut v_a_3171_: *mut LeanObject,
    mut v_a_3172_: *mut LeanObject,
    mut v_a_3173_: *mut LeanObject,
    mut v_a_3174_: *mut LeanObject,
    mut v_a_3175_: *mut LeanObject,
    mut v_a_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3178_: *mut LeanObject = core::ptr::null_mut();
    v_res_3178_ = l_String_reduceGT(
        v_e_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_,
    );
    lean_dec(v_a_3176_);
    lean_dec_ref(v_a_3175_);
    lean_dec(v_a_3174_);
    lean_dec_ref(v_a_3173_);
    lean_dec(v_a_3172_);
    lean_dec_ref(v_a_3171_);
    lean_dec(v_a_3170_);
    return v_res_3178_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    v___x_3184_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_;
    v___x_3185_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_;
    v___x_3186_ = lean_alloc_closure(l_String_reduceGT___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3187_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3184_, v___x_3185_, v___x_3186_);
    return v___x_3187_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20____boxed(
    mut v_a_3188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3189_: *mut LeanObject = core::ptr::null_mut();
    v_res_3189_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_();
    return v_res_3189_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    v___x_3190_ = lean_alloc_closure(l_String_reduceGT___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3191_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3191_, 0, v___x_3190_);
    return v___x_3191_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    v___x_3193_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_;
    v___x_3194_ = 1;
    v___x_3195_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_);
    v___x_3196_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3193_, v___x_3194_, v___x_3195_);
    return v___x_3196_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22____boxed(
    mut v_a_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3198_: *mut LeanObject = core::ptr::null_mut();
    v_res_3198_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_();
    return v_res_3198_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    v___x_3200_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_;
    v___x_3201_ = 1;
    v___x_3202_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_);
    v___x_3203_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3200_, v___x_3201_, v___x_3202_);
    return v___x_3203_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24____boxed(
    mut v_a_3204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3205_: *mut LeanObject = core::ptr::null_mut();
    v_res_3205_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_();
    return v_res_3205_;
}
pub unsafe fn l_String_reduceGE___redArg(
    mut v_e_3211_: *mut LeanObject,
    mut v_a_3212_: *mut LeanObject,
    mut v_a_3213_: *mut LeanObject,
    mut v_a_3214_: *mut LeanObject,
    mut v_a_3215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v_val_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3235_: u8 = 0;
    let mut v_val_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3243_: u8 = 0;
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3217_ = l_String_reduceGE___redArg___closed__2;
                v___x_3218_ = lean_unsigned_to_nat(4);
                v___x_3219_ = l_Lean_Expr_isAppOfArity(v_e_3211_, v___x_3217_, v___x_3218_);
                if v___x_3219_ == 0 {
                    lean_dec_ref(v_e_3211_);
                    v___x_3220_ = l_String_reduceBinPred___redArg___closed__0;
                    v___x_3221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3221_, 0, v___x_3220_);
                    return v___x_3221_;
                } else {
                    v___x_3222_ = l_Lean_Expr_appFn_x21(v_e_3211_);
                    v___x_3223_ = l_Lean_Expr_appArg_x21(v___x_3222_);
                    lean_dec_ref(v___x_3222_);
                    v___x_3224_ = l_String_fromExpr_x3f___redArg(v___x_3223_);
                    v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
                    v_isSharedCheck_3248_ = (!lean_is_exclusive(v___x_3224_)) as u8;
                    if v_isSharedCheck_3248_ == 0 {
                        v___x_3227_ = v___x_3224_;
                        v_isShared_3228_ = v_isSharedCheck_3248_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3225_);
                        lean_dec(v___x_3224_);
                        v___x_3227_ = lean_box(0);
                        v_isShared_3228_ = v_isSharedCheck_3248_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3225_) == 1 {
                    lean_del_object(v___x_3227_);
                    v_val_3229_ = lean_ctor_get(v_a_3225_, 0);
                    lean_inc(v_val_3229_);
                    lean_dec_ref_known(v_a_3225_, 1);
                    v___x_3230_ = l_Lean_Expr_appArg_x21(v_e_3211_);
                    v___x_3231_ = l_String_fromExpr_x3f___redArg(v___x_3230_);
                    v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
                    v_isSharedCheck_3243_ = (!lean_is_exclusive(v___x_3231_)) as u8;
                    if v_isSharedCheck_3243_ == 0 {
                        v___x_3234_ = v___x_3231_;
                        v_isShared_3235_ = v_isSharedCheck_3243_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3232_);
                        lean_dec(v___x_3231_);
                        v___x_3234_ = lean_box(0);
                        v_isShared_3235_ = v_isSharedCheck_3243_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3225_);
                    lean_dec_ref(v_e_3211_);
                    v___x_3244_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3228_ == 0 {
                        lean_ctor_set(v___x_3227_, 0, v___x_3244_);
                        v___x_3246_ = v___x_3227_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
                        v___x_3246_ = v_reuseFailAlloc_3247_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3232_) == 1 {
                    lean_del_object(v___x_3234_);
                    v_val_3236_ = lean_ctor_get(v_a_3232_, 0);
                    lean_inc(v_val_3236_);
                    lean_dec_ref_known(v_a_3232_, 1);
                    v___x_3237_ = l_String_decLE(v_val_3236_, v_val_3229_);
                    lean_dec(v_val_3229_);
                    lean_dec(v_val_3236_);
                    v___x_3238_ = l_Lean_Meta_Simp_evalPropStep___redArg(
                        v_e_3211_,
                        v___x_3237_,
                        v_a_3212_,
                        v_a_3213_,
                        v_a_3214_,
                        v_a_3215_,
                    );
                    return v___x_3238_;
                } else {
                    lean_dec(v_a_3232_);
                    lean_dec(v_val_3229_);
                    lean_dec_ref(v_e_3211_);
                    v___x_3239_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3235_ == 0 {
                        lean_ctor_set(v___x_3234_, 0, v___x_3239_);
                        v___x_3241_ = v___x_3234_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
                        v___x_3241_ = v_reuseFailAlloc_3242_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3241_;
            }
            4 => {
                return v___x_3246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceGE___redArg___boxed(
    mut v_e_3249_: *mut LeanObject,
    mut v_a_3250_: *mut LeanObject,
    mut v_a_3251_: *mut LeanObject,
    mut v_a_3252_: *mut LeanObject,
    mut v_a_3253_: *mut LeanObject,
    mut v_a_3254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3255_: *mut LeanObject = core::ptr::null_mut();
    v_res_3255_ = l_String_reduceGE___redArg(v_e_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
    lean_dec(v_a_3253_);
    lean_dec_ref(v_a_3252_);
    lean_dec(v_a_3251_);
    lean_dec_ref(v_a_3250_);
    return v_res_3255_;
}
pub unsafe fn l_String_reduceGE(
    mut v_e_3256_: *mut LeanObject,
    mut v_a_3257_: *mut LeanObject,
    mut v_a_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
    mut v_a_3263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    v___x_3265_ = l_String_reduceGE___redArg(v_e_3256_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_);
    return v___x_3265_;
}
pub unsafe fn l_String_reduceGE___boxed(
    mut v_e_3266_: *mut LeanObject,
    mut v_a_3267_: *mut LeanObject,
    mut v_a_3268_: *mut LeanObject,
    mut v_a_3269_: *mut LeanObject,
    mut v_a_3270_: *mut LeanObject,
    mut v_a_3271_: *mut LeanObject,
    mut v_a_3272_: *mut LeanObject,
    mut v_a_3273_: *mut LeanObject,
    mut v_a_3274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3275_: *mut LeanObject = core::ptr::null_mut();
    v_res_3275_ = l_String_reduceGE(
        v_e_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_,
    );
    lean_dec(v_a_3273_);
    lean_dec_ref(v_a_3272_);
    lean_dec(v_a_3271_);
    lean_dec_ref(v_a_3270_);
    lean_dec(v_a_3269_);
    lean_dec_ref(v_a_3268_);
    lean_dec(v_a_3267_);
    return v_res_3275_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    v___x_3281_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_;
    v___x_3282_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_;
    v___x_3283_ = lean_alloc_closure(l_String_reduceGE___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3284_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3281_, v___x_3282_, v___x_3283_);
    return v___x_3284_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20____boxed(
    mut v_a_3285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3286_: *mut LeanObject = core::ptr::null_mut();
    v_res_3286_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_();
    return v_res_3286_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    v___x_3287_ = lean_alloc_closure(l_String_reduceGE___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3288_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3288_, 0, v___x_3287_);
    return v___x_3288_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    v___x_3290_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_;
    v___x_3291_ = 1;
    v___x_3292_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_);
    v___x_3293_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3290_, v___x_3291_, v___x_3292_);
    return v___x_3293_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22____boxed(
    mut v_a_3294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_res_3295_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_();
    return v_res_3295_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    v___x_3297_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_;
    v___x_3298_ = 1;
    v___x_3299_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_);
    v___x_3300_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3297_, v___x_3298_, v___x_3299_);
    return v___x_3300_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24____boxed(
    mut v_a_3301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3302_: *mut LeanObject = core::ptr::null_mut();
    v_res_3302_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_();
    return v_res_3302_;
}
pub unsafe fn l_String_reduceEq___lam__0(
    mut v_val_3303_: *mut LeanObject,
    mut v_val_3304_: *mut LeanObject,
    mut v___y_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    v___x_3313_ = l_Lean_Meta_mkStringLitNeProof(
        v_val_3303_,
        v_val_3304_,
        v___y_3308_,
        v___y_3309_,
        v___y_3310_,
        v___y_3311_,
    );
    return v___x_3313_;
}
pub unsafe fn l_String_reduceEq___lam__0___boxed(
    mut v_val_3314_: *mut LeanObject,
    mut v_val_3315_: *mut LeanObject,
    mut v___y_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3324_: *mut LeanObject = core::ptr::null_mut();
    v_res_3324_ = l_String_reduceEq___lam__0(
        v_val_3314_,
        v_val_3315_,
        v___y_3316_,
        v___y_3317_,
        v___y_3318_,
        v___y_3319_,
        v___y_3320_,
        v___y_3321_,
        v___y_3322_,
    );
    lean_dec(v___y_3322_);
    lean_dec_ref(v___y_3321_);
    lean_dec(v___y_3320_);
    lean_dec_ref(v___y_3319_);
    lean_dec(v___y_3318_);
    lean_dec_ref(v___y_3317_);
    lean_dec(v___y_3316_);
    return v_res_3324_;
}
pub unsafe fn l_String_reduceEq(
    mut v_e_3328_: *mut LeanObject,
    mut v_a_3329_: *mut LeanObject,
    mut v_a_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v_val_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3355_: u8 = 0;
    let mut v_val_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3337_ = l_String_reduceEq___closed__1;
                v___x_3338_ = lean_unsigned_to_nat(3);
                v___x_3339_ = l_Lean_Expr_isAppOfArity(v_e_3328_, v___x_3337_, v___x_3338_);
                if v___x_3339_ == 0 {
                    lean_dec_ref(v_e_3328_);
                    v___x_3340_ = l_String_reduceBinPred___redArg___closed__0;
                    v___x_3341_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3341_, 0, v___x_3340_);
                    return v___x_3341_;
                } else {
                    v___x_3342_ = l_Lean_Expr_appFn_x21(v_e_3328_);
                    v___x_3343_ = l_Lean_Expr_appArg_x21(v___x_3342_);
                    lean_dec_ref(v___x_3342_);
                    v___x_3344_ = l_String_fromExpr_x3f___redArg(v___x_3343_);
                    v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
                    v_isSharedCheck_3369_ = (!lean_is_exclusive(v___x_3344_)) as u8;
                    if v_isSharedCheck_3369_ == 0 {
                        v___x_3347_ = v___x_3344_;
                        v_isShared_3348_ = v_isSharedCheck_3369_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3345_);
                        lean_dec(v___x_3344_);
                        v___x_3347_ = lean_box(0);
                        v_isShared_3348_ = v_isSharedCheck_3369_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3345_) == 1 {
                    lean_del_object(v___x_3347_);
                    v_val_3349_ = lean_ctor_get(v_a_3345_, 0);
                    lean_inc(v_val_3349_);
                    lean_dec_ref_known(v_a_3345_, 1);
                    v___x_3350_ = l_Lean_Expr_appArg_x21(v_e_3328_);
                    v___x_3351_ = l_String_fromExpr_x3f___redArg(v___x_3350_);
                    v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
                    v_isSharedCheck_3364_ = (!lean_is_exclusive(v___x_3351_)) as u8;
                    if v_isSharedCheck_3364_ == 0 {
                        v___x_3354_ = v___x_3351_;
                        v_isShared_3355_ = v_isSharedCheck_3364_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3352_);
                        lean_dec(v___x_3351_);
                        v___x_3354_ = lean_box(0);
                        v_isShared_3355_ = v_isSharedCheck_3364_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3345_);
                    lean_dec_ref(v_e_3328_);
                    v___x_3365_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3348_ == 0 {
                        lean_ctor_set(v___x_3347_, 0, v___x_3365_);
                        v___x_3367_ = v___x_3347_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
                        v___x_3367_ = v_reuseFailAlloc_3368_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3352_) == 1 {
                    lean_del_object(v___x_3354_);
                    v_val_3356_ = lean_ctor_get(v_a_3352_, 0);
                    lean_inc_n(v_val_3356_, 2);
                    lean_dec_ref_known(v_a_3352_, 1);
                    lean_inc(v_val_3349_);
                    v___f_3357_ = lean_alloc_closure(
                        l_String_reduceEq___lam__0___boxed as *mut core::ffi::c_void,
                        10,
                        2,
                    );
                    lean_closure_set(v___f_3357_, 0, v_val_3349_);
                    lean_closure_set(v___f_3357_, 1, v_val_3356_);
                    v___x_3358_ = lean_string_dec_eq(v_val_3349_, v_val_3356_);
                    lean_dec(v_val_3356_);
                    lean_dec(v_val_3349_);
                    v___x_3359_ = l_Lean_Meta_Simp_evalEqPropStep(
                        v_e_3328_,
                        v___x_3358_,
                        v___f_3357_,
                        v_a_3329_,
                        v_a_3330_,
                        v_a_3331_,
                        v_a_3332_,
                        v_a_3333_,
                        v_a_3334_,
                        v_a_3335_,
                    );
                    return v___x_3359_;
                } else {
                    lean_dec(v_a_3352_);
                    lean_dec(v_val_3349_);
                    lean_dec_ref(v_e_3328_);
                    v___x_3360_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3355_ == 0 {
                        lean_ctor_set(v___x_3354_, 0, v___x_3360_);
                        v___x_3362_ = v___x_3354_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
                        v___x_3362_ = v_reuseFailAlloc_3363_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3362_;
            }
            4 => {
                return v___x_3367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceEq___boxed(
    mut v_e_3370_: *mut LeanObject,
    mut v_a_3371_: *mut LeanObject,
    mut v_a_3372_: *mut LeanObject,
    mut v_a_3373_: *mut LeanObject,
    mut v_a_3374_: *mut LeanObject,
    mut v_a_3375_: *mut LeanObject,
    mut v_a_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_a_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3379_: *mut LeanObject = core::ptr::null_mut();
    v_res_3379_ = l_String_reduceEq(
        v_e_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_,
    );
    lean_dec(v_a_3377_);
    lean_dec_ref(v_a_3376_);
    lean_dec(v_a_3375_);
    lean_dec_ref(v_a_3374_);
    lean_dec(v_a_3373_);
    lean_dec_ref(v_a_3372_);
    lean_dec(v_a_3371_);
    return v_res_3379_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    v___x_3397_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_;
    v___x_3398_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_;
    v___x_3399_ = lean_alloc_closure(l_String_reduceEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3400_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3397_, v___x_3398_, v___x_3399_);
    return v___x_3400_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20____boxed(
    mut v_a_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3402_: *mut LeanObject = core::ptr::null_mut();
    v_res_3402_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_();
    return v_res_3402_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    v___x_3403_ = lean_alloc_closure(l_String_reduceEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3404_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3404_, 0, v___x_3403_);
    return v___x_3404_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    v___x_3406_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_;
    v___x_3407_ = 1;
    v___x_3408_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_);
    v___x_3409_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3406_, v___x_3407_, v___x_3408_);
    return v___x_3409_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22____boxed(
    mut v_a_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3411_: *mut LeanObject = core::ptr::null_mut();
    v_res_3411_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_();
    return v_res_3411_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: u8 = 0;
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    v___x_3413_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_;
    v___x_3414_ = 1;
    v___x_3415_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_);
    v___x_3416_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3413_, v___x_3414_, v___x_3415_);
    return v___x_3416_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24____boxed(
    mut v_a_3417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3418_: *mut LeanObject = core::ptr::null_mut();
    v_res_3418_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24_();
    return v_res_3418_;
}
pub unsafe fn l_String_reduceNe(
    mut v_e_3422_: *mut LeanObject,
    mut v_a_3423_: *mut LeanObject,
    mut v_a_3424_: *mut LeanObject,
    mut v_a_3425_: *mut LeanObject,
    mut v_a_3426_: *mut LeanObject,
    mut v_a_3427_: *mut LeanObject,
    mut v_a_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v_val_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v_val_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: u8 = 0;
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3460_: u8 = 0;
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3431_ = l_String_reduceNe___closed__1;
                v___x_3432_ = lean_unsigned_to_nat(3);
                v___x_3433_ = l_Lean_Expr_isAppOfArity(v_e_3422_, v___x_3431_, v___x_3432_);
                if v___x_3433_ == 0 {
                    lean_dec_ref(v_e_3422_);
                    v___x_3434_ = l_String_reduceBinPred___redArg___closed__0;
                    v___x_3435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3435_, 0, v___x_3434_);
                    return v___x_3435_;
                } else {
                    v___x_3436_ = l_Lean_Expr_appFn_x21(v_e_3422_);
                    v___x_3437_ = l_Lean_Expr_appArg_x21(v___x_3436_);
                    lean_dec_ref(v___x_3436_);
                    v___x_3438_ = l_String_fromExpr_x3f___redArg(v___x_3437_);
                    v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
                    v_isSharedCheck_3465_ = (!lean_is_exclusive(v___x_3438_)) as u8;
                    if v_isSharedCheck_3465_ == 0 {
                        v___x_3441_ = v___x_3438_;
                        v_isShared_3442_ = v_isSharedCheck_3465_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3439_);
                        lean_dec(v___x_3438_);
                        v___x_3441_ = lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3465_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3439_) == 1 {
                    lean_del_object(v___x_3441_);
                    v_val_3443_ = lean_ctor_get(v_a_3439_, 0);
                    lean_inc(v_val_3443_);
                    lean_dec_ref_known(v_a_3439_, 1);
                    v___x_3444_ = l_Lean_Expr_appArg_x21(v_e_3422_);
                    v___x_3445_ = l_String_fromExpr_x3f___redArg(v___x_3444_);
                    v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
                    v_isSharedCheck_3460_ = (!lean_is_exclusive(v___x_3445_)) as u8;
                    if v_isSharedCheck_3460_ == 0 {
                        v___x_3448_ = v___x_3445_;
                        v_isShared_3449_ = v_isSharedCheck_3460_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3446_);
                        lean_dec(v___x_3445_);
                        v___x_3448_ = lean_box(0);
                        v_isShared_3449_ = v_isSharedCheck_3460_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3439_);
                    lean_dec_ref(v_e_3422_);
                    v___x_3461_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3442_ == 0 {
                        lean_ctor_set(v___x_3441_, 0, v___x_3461_);
                        v___x_3463_ = v___x_3441_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
                        v___x_3463_ = v_reuseFailAlloc_3464_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3446_) == 1 {
                    lean_del_object(v___x_3448_);
                    v_val_3450_ = lean_ctor_get(v_a_3446_, 0);
                    lean_inc_n(v_val_3450_, 2);
                    lean_dec_ref_known(v_a_3446_, 1);
                    lean_inc(v_val_3443_);
                    v___f_3451_ = lean_alloc_closure(
                        l_String_reduceEq___lam__0___boxed as *mut core::ffi::c_void,
                        10,
                        2,
                    );
                    lean_closure_set(v___f_3451_, 0, v_val_3443_);
                    lean_closure_set(v___f_3451_, 1, v_val_3450_);
                    v___x_3452_ = lean_string_dec_eq(v_val_3443_, v_val_3450_);
                    lean_dec(v_val_3450_);
                    lean_dec(v_val_3443_);
                    if v___x_3452_ == 0 {
                        v___x_3453_ = l_Lean_Meta_Simp_evalNePropStep(
                            v_e_3422_,
                            v___x_3433_,
                            v___f_3451_,
                            v_a_3423_,
                            v_a_3424_,
                            v_a_3425_,
                            v_a_3426_,
                            v_a_3427_,
                            v_a_3428_,
                            v_a_3429_,
                        );
                        return v___x_3453_;
                    } else {
                        v___x_3454_ = 0;
                        v___x_3455_ = l_Lean_Meta_Simp_evalNePropStep(
                            v_e_3422_,
                            v___x_3454_,
                            v___f_3451_,
                            v_a_3423_,
                            v_a_3424_,
                            v_a_3425_,
                            v_a_3426_,
                            v_a_3427_,
                            v_a_3428_,
                            v_a_3429_,
                        );
                        return v___x_3455_;
                    }
                } else {
                    lean_dec(v_a_3446_);
                    lean_dec(v_val_3443_);
                    lean_dec_ref(v_e_3422_);
                    v___x_3456_ = l_String_reduceBinPred___redArg___closed__0;
                    if v_isShared_3449_ == 0 {
                        lean_ctor_set(v___x_3448_, 0, v___x_3456_);
                        v___x_3458_ = v___x_3448_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
                        v___x_3458_ = v_reuseFailAlloc_3459_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3458_;
            }
            4 => {
                return v___x_3463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceNe___boxed(
    mut v_e_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
    mut v_a_3468_: *mut LeanObject,
    mut v_a_3469_: *mut LeanObject,
    mut v_a_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
    mut v_a_3472_: *mut LeanObject,
    mut v_a_3473_: *mut LeanObject,
    mut v_a_3474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3475_: *mut LeanObject = core::ptr::null_mut();
    v_res_3475_ = l_String_reduceNe(
        v_e_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_,
    );
    lean_dec(v_a_3473_);
    lean_dec_ref(v_a_3472_);
    lean_dec(v_a_3471_);
    lean_dec_ref(v_a_3470_);
    lean_dec(v_a_3469_);
    lean_dec_ref(v_a_3468_);
    lean_dec(v_a_3467_);
    return v_res_3475_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    v___x_3498_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_;
    v___x_3499_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_;
    v___x_3500_ = lean_alloc_closure(l_String_reduceNe___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3501_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3498_, v___x_3499_, v___x_3500_);
    return v___x_3501_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20____boxed(
    mut v_a_3502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3503_: *mut LeanObject = core::ptr::null_mut();
    v_res_3503_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_();
    return v_res_3503_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    v___x_3504_ = lean_alloc_closure(l_String_reduceNe___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3505_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3505_, 0, v___x_3504_);
    return v___x_3505_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    v___x_3507_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_;
    v___x_3508_ = 1;
    v___x_3509_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_);
    v___x_3510_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3507_, v___x_3508_, v___x_3509_);
    return v___x_3510_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22____boxed(
    mut v_a_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3512_: *mut LeanObject = core::ptr::null_mut();
    v_res_3512_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_();
    return v_res_3512_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: u8 = 0;
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    v___x_3514_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_;
    v___x_3515_ = 1;
    v___x_3516_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_);
    v___x_3517_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3514_, v___x_3515_, v___x_3516_);
    return v___x_3517_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24____boxed(
    mut v_a_3518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3519_: *mut LeanObject = core::ptr::null_mut();
    v_res_3519_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24_();
    return v_res_3519_;
}
pub unsafe fn l_String_reduceBEq___redArg(mut v_e_3525_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v_val_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3542_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3548_: u8 = 0;
    let mut v___y_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3565_: u8 = 0;
    let mut v_isSharedCheck_3566_: u8 = 0;
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3527_ = l_String_reduceBEq___redArg___closed__2;
                v___x_3528_ = lean_unsigned_to_nat(4);
                v___x_3529_ = l_Lean_Expr_isAppOfArity(v_e_3525_, v___x_3527_, v___x_3528_);
                if v___x_3529_ == 0 {
                    v___x_3530_ = l_String_reduceAppend___redArg___closed__3;
                    v___x_3531_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3531_, 0, v___x_3530_);
                    return v___x_3531_;
                } else {
                    v___x_3532_ = l_Lean_Expr_appFn_x21(v_e_3525_);
                    v___x_3533_ = l_Lean_Expr_appArg_x21(v___x_3532_);
                    lean_dec_ref(v___x_3532_);
                    v___x_3534_ = l_String_fromExpr_x3f___redArg(v___x_3533_);
                    v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
                    v_isSharedCheck_3571_ = (!lean_is_exclusive(v___x_3534_)) as u8;
                    if v_isSharedCheck_3571_ == 0 {
                        v___x_3537_ = v___x_3534_;
                        v_isShared_3538_ = v_isSharedCheck_3571_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3535_);
                        lean_dec(v___x_3534_);
                        v___x_3537_ = lean_box(0);
                        v_isShared_3538_ = v_isSharedCheck_3571_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3535_) == 1 {
                    v_val_3539_ = lean_ctor_get(v_a_3535_, 0);
                    v_isSharedCheck_3566_ = (!lean_is_exclusive(v_a_3535_)) as u8;
                    if v_isSharedCheck_3566_ == 0 {
                        v___x_3541_ = v_a_3535_;
                        v_isShared_3542_ = v_isSharedCheck_3566_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3539_);
                        lean_dec(v_a_3535_);
                        v___x_3541_ = lean_box(0);
                        v_isShared_3542_ = v_isSharedCheck_3566_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3535_);
                    v___x_3567_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_3538_ == 0 {
                        lean_ctor_set(v___x_3537_, 0, v___x_3567_);
                        v___x_3569_ = v___x_3537_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
                        v___x_3569_ = v_reuseFailAlloc_3570_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3543_ = l_Lean_Expr_appArg_x21(v_e_3525_);
                v___x_3544_ = l_String_fromExpr_x3f___redArg(v___x_3543_);
                v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
                v_isSharedCheck_3565_ = (!lean_is_exclusive(v___x_3544_)) as u8;
                if v_isSharedCheck_3565_ == 0 {
                    v___x_3547_ = v___x_3544_;
                    v_isShared_3548_ = v_isSharedCheck_3565_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_3545_);
                    lean_dec(v___x_3544_);
                    v___x_3547_ = lean_box(0);
                    v_isShared_3548_ = v_isSharedCheck_3565_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_a_3545_) == 1 {
                    lean_del_object(v___x_3537_);
                    v_val_3557_ = lean_ctor_get(v_a_3545_, 0);
                    lean_inc(v_val_3557_);
                    lean_dec_ref_known(v_a_3545_, 1);
                    v___x_3558_ = lean_string_dec_eq(v_val_3539_, v_val_3557_);
                    lean_dec(v_val_3557_);
                    lean_dec(v_val_3539_);
                    if v___x_3558_ == 0 {
                        v___x_3559_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_String_reduceBoolPred___redArg___closed__3),
                            core::ptr::addr_of_mut!(
                                l_String_reduceBoolPred___redArg___closed__3_once
                            ),
                            _init_l_String_reduceBoolPred___redArg___closed__3,
                        );
                        v___y_3550_ = v___x_3559_;
                        state = 4;
                        continue;
                    } else {
                        v___x_3560_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_String_reduceBoolPred___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_String_reduceBoolPred___redArg___closed__6_once
                            ),
                            _init_l_String_reduceBoolPred___redArg___closed__6,
                        );
                        v___y_3550_ = v___x_3560_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3547_);
                    lean_dec(v_a_3545_);
                    lean_del_object(v___x_3541_);
                    lean_dec(v_val_3539_);
                    v___x_3561_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_3538_ == 0 {
                        lean_ctor_set(v___x_3537_, 0, v___x_3561_);
                        v___x_3563_ = v___x_3537_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
                        v___x_3563_ = v_reuseFailAlloc_3564_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                lean_inc_ref(v___y_3550_);
                if v_isShared_3542_ == 0 {
                    lean_ctor_set_tag(v___x_3541_, 0);
                    lean_ctor_set(v___x_3541_, 0, v___y_3550_);
                    v___x_3552_ = v___x_3541_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___y_3550_);
                    v___x_3552_ = v_reuseFailAlloc_3556_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3548_ == 0 {
                    lean_ctor_set(v___x_3547_, 0, v___x_3552_);
                    v___x_3554_ = v___x_3547_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
                    v___x_3554_ = v_reuseFailAlloc_3555_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3554_;
            }
            7 => {
                return v___x_3563_;
            }
            8 => {
                return v___x_3569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceBEq___redArg___boxed(
    mut v_e_3572_: *mut LeanObject,
    mut v_a_3573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3574_: *mut LeanObject = core::ptr::null_mut();
    v_res_3574_ = l_String_reduceBEq___redArg(v_e_3572_);
    lean_dec_ref(v_e_3572_);
    return v_res_3574_;
}
pub unsafe fn l_String_reduceBEq(
    mut v_e_3575_: *mut LeanObject,
    mut v_a_3576_: *mut LeanObject,
    mut v_a_3577_: *mut LeanObject,
    mut v_a_3578_: *mut LeanObject,
    mut v_a_3579_: *mut LeanObject,
    mut v_a_3580_: *mut LeanObject,
    mut v_a_3581_: *mut LeanObject,
    mut v_a_3582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    v___x_3584_ = l_String_reduceBEq___redArg(v_e_3575_);
    return v___x_3584_;
}
pub unsafe fn l_String_reduceBEq___boxed(
    mut v_e_3585_: *mut LeanObject,
    mut v_a_3586_: *mut LeanObject,
    mut v_a_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
    mut v_a_3590_: *mut LeanObject,
    mut v_a_3591_: *mut LeanObject,
    mut v_a_3592_: *mut LeanObject,
    mut v_a_3593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3594_: *mut LeanObject = core::ptr::null_mut();
    v_res_3594_ = l_String_reduceBEq(
        v_e_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_,
    );
    lean_dec(v_a_3592_);
    lean_dec_ref(v_a_3591_);
    lean_dec(v_a_3590_);
    lean_dec_ref(v_a_3589_);
    lean_dec(v_a_3588_);
    lean_dec_ref(v_a_3587_);
    lean_dec(v_a_3586_);
    lean_dec_ref(v_e_3585_);
    return v_res_3594_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    v___x_3613_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_;
    v___x_3614_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_;
    v___x_3615_ = lean_alloc_closure(l_String_reduceBEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3616_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3613_, v___x_3614_, v___x_3615_);
    return v___x_3616_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20____boxed(
    mut v_a_3617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3618_: *mut LeanObject = core::ptr::null_mut();
    v_res_3618_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_();
    return v_res_3618_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    v___x_3619_ = lean_alloc_closure(l_String_reduceBEq___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3620_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3620_, 0, v___x_3619_);
    return v___x_3620_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    v___x_3622_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_;
    v___x_3623_ = 1;
    v___x_3624_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_);
    v___x_3625_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3622_, v___x_3623_, v___x_3624_);
    return v___x_3625_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22____boxed(
    mut v_a_3626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3627_: *mut LeanObject = core::ptr::null_mut();
    v_res_3627_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_();
    return v_res_3627_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: u8 = 0;
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    v___x_3629_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_;
    v___x_3630_ = 1;
    v___x_3631_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_);
    v___x_3632_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3629_, v___x_3630_, v___x_3631_);
    return v___x_3632_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24____boxed(
    mut v_a_3633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3634_: *mut LeanObject = core::ptr::null_mut();
    v_res_3634_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_();
    return v_res_3634_;
}
pub unsafe fn l_String_reduceBNe___redArg(mut v_e_3638_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v_val_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3655_: u8 = 0;
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___y_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3679_: u8 = 0;
    let mut v_isSharedCheck_3680_: u8 = 0;
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3640_ = l_String_reduceBNe___redArg___closed__1;
                v___x_3641_ = lean_unsigned_to_nat(4);
                v___x_3642_ = l_Lean_Expr_isAppOfArity(v_e_3638_, v___x_3640_, v___x_3641_);
                if v___x_3642_ == 0 {
                    v___x_3643_ = l_String_reduceAppend___redArg___closed__3;
                    v___x_3644_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                    return v___x_3644_;
                } else {
                    v___x_3645_ = l_Lean_Expr_appFn_x21(v_e_3638_);
                    v___x_3646_ = l_Lean_Expr_appArg_x21(v___x_3645_);
                    lean_dec_ref(v___x_3645_);
                    v___x_3647_ = l_String_fromExpr_x3f___redArg(v___x_3646_);
                    v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
                    v_isSharedCheck_3685_ = (!lean_is_exclusive(v___x_3647_)) as u8;
                    if v_isSharedCheck_3685_ == 0 {
                        v___x_3650_ = v___x_3647_;
                        v_isShared_3651_ = v_isSharedCheck_3685_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3648_);
                        lean_dec(v___x_3647_);
                        v___x_3650_ = lean_box(0);
                        v_isShared_3651_ = v_isSharedCheck_3685_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3648_) == 1 {
                    v_val_3652_ = lean_ctor_get(v_a_3648_, 0);
                    v_isSharedCheck_3680_ = (!lean_is_exclusive(v_a_3648_)) as u8;
                    if v_isSharedCheck_3680_ == 0 {
                        v___x_3654_ = v_a_3648_;
                        v_isShared_3655_ = v_isSharedCheck_3680_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3652_);
                        lean_dec(v_a_3648_);
                        v___x_3654_ = lean_box(0);
                        v_isShared_3655_ = v_isSharedCheck_3680_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3648_);
                    v___x_3681_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_3651_ == 0 {
                        lean_ctor_set(v___x_3650_, 0, v___x_3681_);
                        v___x_3683_ = v___x_3650_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
                        v___x_3683_ = v_reuseFailAlloc_3684_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3656_ = l_Lean_Expr_appArg_x21(v_e_3638_);
                v___x_3657_ = l_String_fromExpr_x3f___redArg(v___x_3656_);
                v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
                v_isSharedCheck_3679_ = (!lean_is_exclusive(v___x_3657_)) as u8;
                if v_isSharedCheck_3679_ == 0 {
                    v___x_3660_ = v___x_3657_;
                    v_isShared_3661_ = v_isSharedCheck_3679_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_3658_);
                    lean_dec(v___x_3657_);
                    v___x_3660_ = lean_box(0);
                    v_isShared_3661_ = v_isSharedCheck_3679_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_a_3658_) == 1 {
                    lean_del_object(v___x_3650_);
                    v_val_3672_ = lean_ctor_get(v_a_3658_, 0);
                    lean_inc(v_val_3672_);
                    lean_dec_ref_known(v_a_3658_, 1);
                    v___x_3673_ = lean_string_dec_eq(v_val_3652_, v_val_3672_);
                    lean_dec(v_val_3672_);
                    lean_dec(v_val_3652_);
                    if v___x_3673_ == 0 {
                        if v___x_3642_ == 0 {
                            state = 7;
                            continue;
                        } else {
                            v___x_3674_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_String_reduceBoolPred___redArg___closed__6
                                ),
                                core::ptr::addr_of_mut!(
                                    l_String_reduceBoolPred___redArg___closed__6_once
                                ),
                                _init_l_String_reduceBoolPred___redArg___closed__6,
                            );
                            v___y_3663_ = v___x_3674_;
                            state = 4;
                            continue;
                        }
                    } else {
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3660_);
                    lean_dec(v_a_3658_);
                    lean_del_object(v___x_3654_);
                    lean_dec(v_val_3652_);
                    v___x_3675_ = l_String_reduceAppend___redArg___closed__3;
                    if v_isShared_3651_ == 0 {
                        lean_ctor_set(v___x_3650_, 0, v___x_3675_);
                        v___x_3677_ = v___x_3650_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
                        v___x_3677_ = v_reuseFailAlloc_3678_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                lean_inc_ref(v___y_3663_);
                if v_isShared_3655_ == 0 {
                    lean_ctor_set_tag(v___x_3654_, 0);
                    lean_ctor_set(v___x_3654_, 0, v___y_3663_);
                    v___x_3665_ = v___x_3654_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___y_3663_);
                    v___x_3665_ = v_reuseFailAlloc_3669_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3661_ == 0 {
                    lean_ctor_set(v___x_3660_, 0, v___x_3665_);
                    v___x_3667_ = v___x_3660_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
                    v___x_3667_ = v_reuseFailAlloc_3668_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3667_;
            }
            7 => {
                v___x_3671_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_String_reduceBoolPred___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_String_reduceBoolPred___redArg___closed__3_once),
                    _init_l_String_reduceBoolPred___redArg___closed__3,
                );
                v___y_3663_ = v___x_3671_;
                state = 4;
                continue;
            }
            8 => {
                return v___x_3677_;
            }
            9 => {
                return v___x_3683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_reduceBNe___redArg___boxed(
    mut v_e_3686_: *mut LeanObject,
    mut v_a_3687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3688_: *mut LeanObject = core::ptr::null_mut();
    v_res_3688_ = l_String_reduceBNe___redArg(v_e_3686_);
    lean_dec_ref(v_e_3686_);
    return v_res_3688_;
}
pub unsafe fn l_String_reduceBNe(
    mut v_e_3689_: *mut LeanObject,
    mut v_a_3690_: *mut LeanObject,
    mut v_a_3691_: *mut LeanObject,
    mut v_a_3692_: *mut LeanObject,
    mut v_a_3693_: *mut LeanObject,
    mut v_a_3694_: *mut LeanObject,
    mut v_a_3695_: *mut LeanObject,
    mut v_a_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    v___x_3698_ = l_String_reduceBNe___redArg(v_e_3689_);
    return v___x_3698_;
}
pub unsafe fn l_String_reduceBNe___boxed(
    mut v_e_3699_: *mut LeanObject,
    mut v_a_3700_: *mut LeanObject,
    mut v_a_3701_: *mut LeanObject,
    mut v_a_3702_: *mut LeanObject,
    mut v_a_3703_: *mut LeanObject,
    mut v_a_3704_: *mut LeanObject,
    mut v_a_3705_: *mut LeanObject,
    mut v_a_3706_: *mut LeanObject,
    mut v_a_3707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3708_: *mut LeanObject = core::ptr::null_mut();
    v_res_3708_ = l_String_reduceBNe(
        v_e_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_,
    );
    lean_dec(v_a_3706_);
    lean_dec_ref(v_a_3705_);
    lean_dec(v_a_3704_);
    lean_dec_ref(v_a_3703_);
    lean_dec(v_a_3702_);
    lean_dec_ref(v_a_3701_);
    lean_dec(v_a_3700_);
    lean_dec_ref(v_e_3699_);
    return v_res_3708_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_()
-> *mut LeanObject {
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    v___x_3727_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_;
    v___x_3728_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_;
    v___x_3729_ = lean_alloc_closure(l_String_reduceBNe___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3730_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_3727_, v___x_3728_, v___x_3729_);
    return v___x_3730_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20____boxed(
    mut v_a_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3732_: *mut LeanObject = core::ptr::null_mut();
    v_res_3732_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_();
    return v_res_3732_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    v___x_3733_ = lean_alloc_closure(l_String_reduceBNe___boxed as *mut core::ffi::c_void, 9, 0);
    v___x_3734_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3734_, 0, v___x_3733_);
    return v___x_3734_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_()
-> *mut LeanObject {
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    v___x_3736_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_;
    v___x_3737_ = 1;
    v___x_3738_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_);
    v___x_3739_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_3736_, v___x_3737_, v___x_3738_);
    return v___x_3739_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22____boxed(
    mut v_a_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3741_: *mut LeanObject = core::ptr::null_mut();
    v_res_3741_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_();
    return v_res_3741_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_()
-> *mut LeanObject {
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3743_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_;
    v___x_3744_ = 1;
    v___x_3745_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22__once), _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_);
    v___x_3746_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v___x_3743_, v___x_3744_, v___x_3745_);
    return v___x_3746_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24____boxed(
    mut v_a_3747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3748_: *mut LeanObject = core::ptr::null_mut();
    v_res_3748_ = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_();
    return v_res_3748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_StringLitProof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceAppend_declare__9_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_19_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_21_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceAppend___regBuiltin_String_reduceAppend_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3308400319____hygCtx___hyg_23_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceOfList_declare__18_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_13_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_15_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceOfList___regBuiltin_String_reduceOfList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1479931662____hygCtx___hyg_17_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToList_declare__23_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_13_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_15_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceToList___regBuiltin_String_reduceToList_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_3121146276____hygCtx___hyg_17_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reducePush_declare__28_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_14_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_16_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reducePush___regBuiltin_String_reducePush_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1574800046____hygCtx___hyg_18_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceSingleton_declare__33_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_13_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_15_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceSingleton___regBuiltin_String_reduceSingleton_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1230273638____hygCtx___hyg_17_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceToSingleton_declare__38_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1880751532____hygCtx___hyg_12_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLT_declare__49_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLT___regBuiltin_String_reduceLT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2485666669____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceLE_declare__54_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceLE___regBuiltin_String_reduceLE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_974433241____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGT_declare__59_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGT___regBuiltin_String_reduceGT_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1929753295____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceGE_declare__64_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceGE___regBuiltin_String_reduceGE_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_2055768308____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceEq_declare__69_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceEq___regBuiltin_String_reduceEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_655475629____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceNe_declare__74_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceNe___regBuiltin_String_reduceNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1425966421____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBEq_declare__79_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBEq___regBuiltin_String_reduceBEq_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_1490231450____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0____regBuiltin_String_reduceBNe_declare__84_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_20_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_22_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_0__String_reduceBNe___regBuiltin_String_reduceBNe_declare__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String_904556020____hygCtx___hyg_24_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_StringLitProof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(builtin);
}
