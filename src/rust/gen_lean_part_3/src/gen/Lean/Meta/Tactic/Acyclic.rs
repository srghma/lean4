// Lean compiler output
// Module: Lean.Meta.Tactic.Acyclic
// Imports: Lean.Meta.MatchUtil Lean.Meta.Tactic.Simp.Main
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isFVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAppM, l_Lean_Meta_mkCongrArg, l_Lean_Meta_mkEqSymm, l_Lean_Meta_mkFalseElim,
    l_Lean_Meta_mkLT,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp_x27;
use crate::r#gen::Lean::Meta::MatchUtil::{
    initialize_Lean_Meta_MatchUtil, runtime_initialize_Lean_Meta_MatchUtil,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::l_Lean_Meta_getSimpTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_simpTarget,
    runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::Util::FindExpr::l_Lean_Expr_occurs;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__2_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 99, 121, 99, 108, 105, 99, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__2_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value
        ) as *mut leanh::LeanObject,
        142734480563613395 as *mut leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value
        ) as *mut leanh::LeanObject,
        15847151208953044930 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__2_value
        ) as *mut leanh::LeanObject,
        13389739805171425583 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__4_value
        ) as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [102, 97, 105, 108, 101, 100, 32, 119, 105, 116, 104, 10, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [83, 105, 122, 101, 79, 102, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 105, 122, 101, 79, 102, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__9_value
        ) as *mut leanh::LeanObject,
        14284789806808743489 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__10_value
        ) as *mut leanh::LeanObject,
        12327557493852523927 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12_value:
    leanh::LeanCtorObject<7> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 32) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((100000 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        72058697861300480 as *mut leanh::LeanObject,
        1103806660609 as *mut leanh::LeanObject,
        72340172838076672 as *mut leanh::LeanObject,
        257 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18_value:
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
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
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
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        108, 116, 95, 111, 102, 95, 108, 116, 95, 111, 102, 95, 101, 113, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value
        ) as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__25_value
        ) as *mut leanh::LeanObject,
        1396935015313227646 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 116, 95, 105, 114, 114, 101, 102, 108, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__24_value
        ) as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__27_value
        ) as *mut leanh::LeanObject,
        11537840754400497528 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [115, 117, 99, 99, 101, 101, 100, 101, 100, 0],
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_acyclic___lam__0___closed__0_value: leanh::LeanStringObject<3> =
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
static mut l_Lean_MVarId_acyclic___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_acyclic___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_acyclic___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_acyclic___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_acyclic___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_acyclic___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_acyclic___lam__0___closed__2_value: leanh::LeanStringObject<7> =
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
        m_data: [116, 121, 112, 101, 58, 32, 0],
    };
static mut l_Lean_MVarId_acyclic___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_acyclic___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_acyclic___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_acyclic___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__0_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__0_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__0_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__1_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__0_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__1_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__1_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__3_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__1_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__3_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__3_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__4_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__3_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__4_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__4_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__5_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__4_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__5_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__5_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [65, 99, 121, 99, 108, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__7_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__5_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10302126120447231702 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__7_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__7_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__8_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__7_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,3992279931632516351 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__8_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__8_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__9_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__8_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17101703385311161906 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__9_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__9_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__10_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [77, 86, 97, 114, 73, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__10_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__10_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__11_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__9_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__10_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14061524436615289165 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__11_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__11_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__12_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__12_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__12_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__13_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__11_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__12_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7148244348172424868 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__13_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__13_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__14_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__14_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__14_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__15_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__13_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__14_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9696806166092535725 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__15_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__15_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__16_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__15_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__2_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7763559545488541208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__16_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__16_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__17_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__16_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__0_value) as *mut leanh::LeanObject,2269267153271413300 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__17_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__17_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__18_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__17_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__1_value) as *mut leanh::LeanObject,1944021572045518241 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__18_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__18_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__19_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__18_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__6_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10300249632404608716 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__19_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__19_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__20_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__19_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1360063758 as usize) << 1) | 1) as *mut leanh::LeanObject,945932630926639216 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__20_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__20_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__21_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__21_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__21_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__22_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__20_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__21_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6692586000668557095 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__22_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__22_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__23_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__23_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__23_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__24_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__22_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__23_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10325962502841254895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__24_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__24_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__24_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,1472431258334110186 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(
    mut v_lhs_893_: *mut leanh::LeanObject,
    mut v_rhs_894_: *mut leanh::LeanObject,
    mut v_a_895_: *mut leanh::LeanObject,
    mut v_a_896_: *mut leanh::LeanObject,
    mut v_a_897_: *mut leanh::LeanObject,
    mut v_a_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: u8 = 0;
    let mut v___x_905_: u8 = 0;
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_904_ = l_Lean_Expr_isFVar(v_lhs_893_);
                if v___x_904_ == 0 {
                    leanh::lean_dec_ref(v_rhs_894_);
                    leanh::lean_dec_ref(v_lhs_893_);
                    state = 1;
                    continue;
                } else {
                    v___x_905_ = l_Lean_Expr_occurs(v_lhs_893_, v_rhs_894_);
                    if v___x_905_ == 0 {
                        leanh::lean_dec_ref(v_rhs_894_);
                        state = 1;
                        continue;
                    } else {
                        v___x_906_ = l_Lean_Meta_isConstructorApp_x27(
                            v_rhs_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_,
                        );
                        return v___x_906_;
                    }
                }
            }
            1 => {
                v___x_901_ = 0;
                v___x_902_ = leanh::lean_box((v___x_901_) as usize);
                v___x_903_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_903_, 0, v___x_902_);
                return v___x_903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget___boxed(
    mut v_lhs_907_: *mut leanh::LeanObject,
    mut v_rhs_908_: *mut leanh::LeanObject,
    mut v_a_909_: *mut leanh::LeanObject,
    mut v_a_910_: *mut leanh::LeanObject,
    mut v_a_911_: *mut leanh::LeanObject,
    mut v_a_912_: *mut leanh::LeanObject,
    mut v_a_913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_914_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(
        v_lhs_907_, v_rhs_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_,
    );
    leanh::lean_dec(v_a_912_);
    leanh::lean_dec_ref(v_a_911_);
    leanh::lean_dec(v_a_910_);
    leanh::lean_dec_ref(v_a_909_);
    return v_res_914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(
    mut v___y_915_: u8,
    mut v_____r_916_: *mut leanh::LeanObject,
    mut v___y_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
    mut v___y_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_922_ = leanh::lean_box((v___y_915_) as usize);
    v___x_923_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_923_, 0, v___x_922_);
    v___x_924_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_924_, 0, v___x_923_);
    return v___x_924_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed(
    mut v___y_925_: *mut leanh::LeanObject,
    mut v_____r_926_: *mut leanh::LeanObject,
    mut v___y_927_: *mut leanh::LeanObject,
    mut v___y_928_: *mut leanh::LeanObject,
    mut v___y_929_: *mut leanh::LeanObject,
    mut v___y_930_: *mut leanh::LeanObject,
    mut v___y_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_9178__boxed_932_: u8 = 0;
    let mut v_res_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_9178__boxed_932_ = (leanh::lean_unbox(v___y_925_) as u8);
    v_res_933_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(
        v___y_9178__boxed_932_,
        v_____r_926_,
        v___y_927_,
        v___y_928_,
        v___y_929_,
        v___y_930_,
    );
    leanh::lean_dec(v___y_930_);
    leanh::lean_dec_ref(v___y_929_);
    leanh::lean_dec(v___y_928_);
    leanh::lean_dec_ref(v___y_927_);
    return v_res_933_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(
    mut v___x_934_: u8,
    mut v_____r_935_: *mut leanh::LeanObject,
    mut v___y_936_: *mut leanh::LeanObject,
    mut v___y_937_: *mut leanh::LeanObject,
    mut v___y_938_: *mut leanh::LeanObject,
    mut v___y_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ = leanh::lean_box((v___x_934_) as usize);
    v___x_942_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_942_, 0, v___x_941_);
    v___x_943_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_943_, 0, v___x_942_);
    return v___x_943_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1___boxed(
    mut v___x_944_: *mut leanh::LeanObject,
    mut v_____r_945_: *mut leanh::LeanObject,
    mut v___y_946_: *mut leanh::LeanObject,
    mut v___y_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
    mut v___y_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9205__boxed_951_: u8 = 0;
    let mut v_res_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9205__boxed_951_ = (leanh::lean_unbox(v___x_944_) as u8);
    v_res_952_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(
        v___x_9205__boxed_951_,
        v_____r_945_,
        v___y_946_,
        v___y_947_,
        v___y_948_,
        v___y_949_,
    );
    leanh::lean_dec(v___y_949_);
    leanh::lean_dec_ref(v___y_948_);
    leanh::lean_dec(v___y_947_);
    leanh::lean_dec_ref(v___y_946_);
    return v_res_952_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(
    mut v_msgData_953_: *mut leanh::LeanObject,
    mut v___y_954_: *mut leanh::LeanObject,
    mut v___y_955_: *mut leanh::LeanObject,
    mut v___y_956_: *mut leanh::LeanObject,
    mut v___y_957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_959_ = lean_st_ref_get(v___y_957_);
    v_env_960_ = leanh::lean_ctor_get(v___x_959_, 0);
    leanh::lean_inc_ref(v_env_960_);
    leanh::lean_dec(v___x_959_);
    v___x_961_ = lean_st_ref_get(v___y_955_);
    v_mctx_962_ = leanh::lean_ctor_get(v___x_961_, 0);
    leanh::lean_inc_ref(v_mctx_962_);
    leanh::lean_dec(v___x_961_);
    v_lctx_963_ = leanh::lean_ctor_get(v___y_954_, 2);
    v_options_964_ = leanh::lean_ctor_get(v___y_956_, 2);
    leanh::lean_inc_ref(v_options_964_);
    leanh::lean_inc_ref(v_lctx_963_);
    v___x_965_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_965_, 0, v_env_960_);
    leanh::lean_ctor_set(v___x_965_, 1, v_mctx_962_);
    leanh::lean_ctor_set(v___x_965_, 2, v_lctx_963_);
    leanh::lean_ctor_set(v___x_965_, 3, v_options_964_);
    v___x_966_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_966_, 0, v___x_965_);
    leanh::lean_ctor_set(v___x_966_, 1, v_msgData_953_);
    v___x_967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_967_, 0, v___x_966_);
    return v___x_967_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0___boxed(
    mut v_msgData_968_: *mut leanh::LeanObject,
    mut v___y_969_: *mut leanh::LeanObject,
    mut v___y_970_: *mut leanh::LeanObject,
    mut v___y_971_: *mut leanh::LeanObject,
    mut v___y_972_: *mut leanh::LeanObject,
    mut v___y_973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_974_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msgData_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
    leanh::lean_dec(v___y_972_);
    leanh::lean_dec_ref(v___y_971_);
    leanh::lean_dec(v___y_970_);
    leanh::lean_dec_ref(v___y_969_);
    return v_res_974_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0()
-> f64 {
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: f64 = 0.0;
    v___x_975_ = leanh::lean_unsigned_to_nat(0);
    v___x_976_ = lean_float_of_nat(v___x_975_);
    return v___x_976_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(
    mut v_cls_980_: *mut leanh::LeanObject,
    mut v_msg_981_: *mut leanh::LeanObject,
    mut v___y_982_: *mut leanh::LeanObject,
    mut v___y_983_: *mut leanh::LeanObject,
    mut v___y_984_: *mut leanh::LeanObject,
    mut v___y_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_992_: u8 = 0;
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1005_: u8 = 0;
    let mut v_tid_1006_: u64 = 0;
    let mut v_traces_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1010_: u8 = 0;
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: f64 = 0.0;
    let mut v___x_1013_: u8 = 0;
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut v_isSharedCheck_1032_: u8 = 0;
    let mut v_isSharedCheck_1033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_987_ = leanh::lean_ctor_get(v___y_984_, 5);
                v___x_988_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0_spec__0(v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
                v_a_989_ = leanh::lean_ctor_get(v___x_988_, 0);
                v_isSharedCheck_1033_ = (!leanh::lean_is_exclusive(v___x_988_)) as u8;
                if v_isSharedCheck_1033_ == 0 {
                    v___x_991_ = v___x_988_;
                    v_isShared_992_ = v_isSharedCheck_1033_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_989_);
                    leanh::lean_dec(v___x_988_);
                    v___x_991_ = leanh::lean_box(0);
                    v_isShared_992_ = v_isSharedCheck_1033_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_993_ = lean_st_ref_take(v___y_985_);
                v_traceState_994_ = leanh::lean_ctor_get(v___x_993_, 4);
                v_env_995_ = leanh::lean_ctor_get(v___x_993_, 0);
                v_nextMacroScope_996_ = leanh::lean_ctor_get(v___x_993_, 1);
                v_ngen_997_ = leanh::lean_ctor_get(v___x_993_, 2);
                v_auxDeclNGen_998_ = leanh::lean_ctor_get(v___x_993_, 3);
                v_cache_999_ = leanh::lean_ctor_get(v___x_993_, 5);
                v_messages_1000_ = leanh::lean_ctor_get(v___x_993_, 6);
                v_infoState_1001_ = leanh::lean_ctor_get(v___x_993_, 7);
                v_snapshotTasks_1002_ = leanh::lean_ctor_get(v___x_993_, 8);
                v_isSharedCheck_1032_ = (!leanh::lean_is_exclusive(v___x_993_)) as u8;
                if v_isSharedCheck_1032_ == 0 {
                    v___x_1004_ = v___x_993_;
                    v_isShared_1005_ = v_isSharedCheck_1032_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1002_);
                    leanh::lean_inc(v_infoState_1001_);
                    leanh::lean_inc(v_messages_1000_);
                    leanh::lean_inc(v_cache_999_);
                    leanh::lean_inc(v_traceState_994_);
                    leanh::lean_inc(v_auxDeclNGen_998_);
                    leanh::lean_inc(v_ngen_997_);
                    leanh::lean_inc(v_nextMacroScope_996_);
                    leanh::lean_inc(v_env_995_);
                    leanh::lean_dec(v___x_993_);
                    v___x_1004_ = leanh::lean_box(0);
                    v_isShared_1005_ = v_isSharedCheck_1032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1006_ = leanh::lean_ctor_get_uint64(
                    v_traceState_994_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1007_ = leanh::lean_ctor_get(v_traceState_994_, 0);
                v_isSharedCheck_1031_ = (!leanh::lean_is_exclusive(v_traceState_994_)) as u8;
                if v_isSharedCheck_1031_ == 0 {
                    v___x_1009_ = v_traceState_994_;
                    v_isShared_1010_ = v_isSharedCheck_1031_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_1007_);
                    leanh::lean_dec(v_traceState_994_);
                    v___x_1009_ = leanh::lean_box(0);
                    v_isShared_1010_ = v_isSharedCheck_1031_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1011_ = leanh::lean_box(0);
                v___x_1012_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__0);
                v___x_1013_ = 0;
                v___x_1014_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__1;
                v___x_1015_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_1015_, 0, v_cls_980_);
                leanh::lean_ctor_set(v___x_1015_, 1, v___x_1011_);
                leanh::lean_ctor_set(v___x_1015_, 2, v___x_1014_);
                leanh::lean_ctor_set_float(
                    v___x_1015_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1012_,
                );
                leanh::lean_ctor_set_float(
                    v___x_1015_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1012_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1015_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1013_,
                );
                v___x_1016_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___closed__2;
                v___x_1017_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1017_, 0, v___x_1015_);
                leanh::lean_ctor_set(v___x_1017_, 1, v_a_989_);
                leanh::lean_ctor_set(v___x_1017_, 2, v___x_1016_);
                leanh::lean_inc(v_ref_987_);
                v___x_1018_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1018_, 0, v_ref_987_);
                leanh::lean_ctor_set(v___x_1018_, 1, v___x_1017_);
                v___x_1019_ = l_Lean_PersistentArray_push___redArg(v_traces_1007_, v___x_1018_);
                if v_isShared_1010_ == 0 {
                    leanh::lean_ctor_set(v___x_1009_, 0, v___x_1019_);
                    v___x_1021_ = v___x_1009_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1019_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1030_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_1006_,
                    );
                    v___x_1021_ = v_reuseFailAlloc_1030_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1005_ == 0 {
                    leanh::lean_ctor_set(v___x_1004_, 4, v___x_1021_);
                    v___x_1023_ = v___x_1004_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1029_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_env_995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_nextMacroScope_996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_ngen_997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_auxDeclNGen_998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 4, v___x_1021_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 5, v_cache_999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 6, v_messages_1000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 7, v_infoState_1001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 8, v_snapshotTasks_1002_);
                    v___x_1023_ = v_reuseFailAlloc_1029_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1024_ = lean_st_ref_set(v___y_985_, v___x_1023_);
                v___x_1025_ = leanh::lean_box(0);
                if v_isShared_992_ == 0 {
                    leanh::lean_ctor_set(v___x_991_, 0, v___x_1025_);
                    v___x_1027_ = v___x_991_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1028_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
                    v___x_1027_ = v_reuseFailAlloc_1028_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1027_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0___boxed(
    mut v_cls_1034_: *mut leanh::LeanObject,
    mut v_msg_1035_: *mut leanh::LeanObject,
    mut v___y_1036_: *mut leanh::LeanObject,
    mut v___y_1037_: *mut leanh::LeanObject,
    mut v___y_1038_: *mut leanh::LeanObject,
    mut v___y_1039_: *mut leanh::LeanObject,
    mut v___y_1040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1041_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v_cls_1034_, v_msg_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
    leanh::lean_dec(v___y_1039_);
    leanh::lean_dec_ref(v___y_1038_);
    leanh::lean_dec(v___y_1037_);
    leanh::lean_dec_ref(v___y_1036_);
    return v_res_1041_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_x_1042_: *mut leanh::LeanObject,
    mut v_x_1043_: *mut leanh::LeanObject,
    mut v_x_1044_: *mut leanh::LeanObject,
    mut v_x_1045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1050_: u8 = 0;
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: u8 = 0;
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: u8 = 0;
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1046_ = leanh::lean_ctor_get(v_x_1042_, 0);
                v_vs_1047_ = leanh::lean_ctor_get(v_x_1042_, 1);
                v_isSharedCheck_1071_ = (!leanh::lean_is_exclusive(v_x_1042_)) as u8;
                if v_isSharedCheck_1071_ == 0 {
                    v___x_1049_ = v_x_1042_;
                    v_isShared_1050_ = v_isSharedCheck_1071_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1047_);
                    leanh::lean_inc(v_ks_1046_);
                    leanh::lean_dec(v_x_1042_);
                    v___x_1049_ = leanh::lean_box(0);
                    v_isShared_1050_ = v_isSharedCheck_1071_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1051_ = lean_array_get_size(v_ks_1046_);
                v___x_1052_ = lean_nat_dec_lt(v_x_1043_, v___x_1051_);
                if v___x_1052_ == 0 {
                    leanh::lean_dec(v_x_1043_);
                    v___x_1053_ = lean_array_push(v_ks_1046_, v_x_1044_);
                    v___x_1054_ = lean_array_push(v_vs_1047_, v_x_1045_);
                    if v_isShared_1050_ == 0 {
                        leanh::lean_ctor_set(v___x_1049_, 1, v___x_1054_);
                        leanh::lean_ctor_set(v___x_1049_, 0, v___x_1053_);
                        v___x_1056_ = v___x_1049_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1057_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1054_);
                        v___x_1056_ = v_reuseFailAlloc_1057_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1058_ = lean_array_fget_borrowed(v_ks_1046_, v_x_1043_);
                    v___x_1059_ = l_Lean_instBEqMVarId_beq(v_x_1044_, v_k_x27_1058_);
                    if v___x_1059_ == 0 {
                        if v_isShared_1050_ == 0 {
                            v___x_1061_ = v___x_1049_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1065_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_ks_1046_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_vs_1047_);
                            v___x_1061_ = v_reuseFailAlloc_1065_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1066_ = lean_array_fset(v_ks_1046_, v_x_1043_, v_x_1044_);
                        v___x_1067_ = lean_array_fset(v_vs_1047_, v_x_1043_, v_x_1045_);
                        leanh::lean_dec(v_x_1043_);
                        if v_isShared_1050_ == 0 {
                            leanh::lean_ctor_set(v___x_1049_, 1, v___x_1067_);
                            leanh::lean_ctor_set(v___x_1049_, 0, v___x_1066_);
                            v___x_1069_ = v___x_1049_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1070_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1066_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1067_);
                            v___x_1069_ = v_reuseFailAlloc_1070_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1056_;
            }
            3 => {
                v___x_1062_ = leanh::lean_unsigned_to_nat(1);
                v___x_1063_ = lean_nat_add(v_x_1043_, v___x_1062_);
                leanh::lean_dec(v_x_1043_);
                v_x_1042_ = v___x_1061_;
                v_x_1043_ = v___x_1063_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_n_1072_: *mut leanh::LeanObject,
    mut v_k_1073_: *mut leanh::LeanObject,
    mut v_v_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1075_ = leanh::lean_unsigned_to_nat(0);
    v___x_1076_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_n_1072_, v___x_1075_, v_k_1073_, v_v_1074_);
    return v___x_1076_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_1077_: usize = 0;
    let mut v___x_1078_: usize = 0;
    let mut v___x_1079_: usize = 0;
    v___x_1077_ = 5usize;
    v___x_1078_ = 1usize;
    v___x_1079_ = lean_usize_shift_left(v___x_1078_, v___x_1077_);
    return v___x_1079_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_1080_: usize = 0;
    let mut v___x_1081_: usize = 0;
    let mut v___x_1082_: usize = 0;
    v___x_1080_ = 1usize;
    v___x_1081_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__0);
    v___x_1082_ = lean_usize_sub(v___x_1081_, v___x_1080_);
    return v___x_1082_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1083_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(
    mut v_x_1084_: *mut leanh::LeanObject,
    mut v_x_1085_: usize,
    mut v_x_1086_: usize,
    mut v_x_1087_: *mut leanh::LeanObject,
    mut v_x_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: usize = 0;
    let mut v___x_1091_: usize = 0;
    let mut v___x_1092_: usize = 0;
    let mut v___x_1093_: usize = 0;
    let mut v_j_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: u8 = 0;
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1099_: u8 = 0;
    let mut v_v_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v___x_1114_: u8 = 0;
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1120_: u8 = 0;
    let mut v_node_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1124_: u8 = 0;
    let mut v___x_1125_: usize = 0;
    let mut v___x_1126_: usize = 0;
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1131_: u8 = 0;
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1133_: u8 = 0;
    let mut v_unused_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1144_: u8 = 0;
    let mut v_ks_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: usize = 0;
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: u8 = 0;
    let mut v_reuseFailAlloc_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1084_) == 0 {
                    v_es_1089_ = leanh::lean_ctor_get(v_x_1084_, 0);
                    v___x_1090_ = 5usize;
                    v___x_1091_ = 1usize;
                    v___x_1092_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__1);
                    v___x_1093_ = lean_usize_land(v_x_1085_, v___x_1092_);
                    v_j_1094_ = lean_usize_to_nat(v___x_1093_);
                    v___x_1095_ = lean_array_get_size(v_es_1089_);
                    v___x_1096_ = lean_nat_dec_lt(v_j_1094_, v___x_1095_);
                    if v___x_1096_ == 0 {
                        leanh::lean_dec(v_j_1094_);
                        leanh::lean_dec(v_x_1088_);
                        leanh::lean_dec(v_x_1087_);
                        return v_x_1084_;
                    } else {
                        leanh::lean_inc_ref(v_es_1089_);
                        v_isSharedCheck_1133_ = (!leanh::lean_is_exclusive(v_x_1084_)) as u8;
                        if v_isSharedCheck_1133_ == 0 {
                            v_unused_1134_ = leanh::lean_ctor_get(v_x_1084_, 0);
                            leanh::lean_dec(v_unused_1134_);
                            v___x_1098_ = v_x_1084_;
                            v_isShared_1099_ = v_isSharedCheck_1133_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1084_);
                            v___x_1098_ = leanh::lean_box(0);
                            v_isShared_1099_ = v_isSharedCheck_1133_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1135_ = leanh::lean_ctor_get(v_x_1084_, 0);
                    v_vs_1136_ = leanh::lean_ctor_get(v_x_1084_, 1);
                    v_isSharedCheck_1156_ = (!leanh::lean_is_exclusive(v_x_1084_)) as u8;
                    if v_isSharedCheck_1156_ == 0 {
                        v___x_1138_ = v_x_1084_;
                        v_isShared_1139_ = v_isSharedCheck_1156_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1136_);
                        leanh::lean_inc(v_ks_1135_);
                        leanh::lean_dec(v_x_1084_);
                        v___x_1138_ = leanh::lean_box(0);
                        v_isShared_1139_ = v_isSharedCheck_1156_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1100_ = lean_array_fget(v_es_1089_, v_j_1094_);
                v___x_1101_ = leanh::lean_box(0);
                v_xs_x27_1102_ = lean_array_fset(v_es_1089_, v_j_1094_, v___x_1101_);
                match leanh::lean_obj_tag(v_v_1100_) {
                    0 => {
                        v_key_1109_ = leanh::lean_ctor_get(v_v_1100_, 0);
                        v_val_1110_ = leanh::lean_ctor_get(v_v_1100_, 1);
                        v_isSharedCheck_1120_ = (!leanh::lean_is_exclusive(v_v_1100_)) as u8;
                        if v_isSharedCheck_1120_ == 0 {
                            v___x_1112_ = v_v_1100_;
                            v_isShared_1113_ = v_isSharedCheck_1120_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1110_);
                            leanh::lean_inc(v_key_1109_);
                            leanh::lean_dec(v_v_1100_);
                            v___x_1112_ = leanh::lean_box(0);
                            v_isShared_1113_ = v_isSharedCheck_1120_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1121_ = leanh::lean_ctor_get(v_v_1100_, 0);
                        v_isSharedCheck_1131_ = (!leanh::lean_is_exclusive(v_v_1100_)) as u8;
                        if v_isSharedCheck_1131_ == 0 {
                            v___x_1123_ = v_v_1100_;
                            v_isShared_1124_ = v_isSharedCheck_1131_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1121_);
                            leanh::lean_dec(v_v_1100_);
                            v___x_1123_ = leanh::lean_box(0);
                            v_isShared_1124_ = v_isSharedCheck_1131_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1132_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1132_, 0, v_x_1087_);
                        leanh::lean_ctor_set(v___x_1132_, 1, v_x_1088_);
                        v___y_1104_ = v___x_1132_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1105_ = lean_array_fset(v_xs_x27_1102_, v_j_1094_, v___y_1104_);
                leanh::lean_dec(v_j_1094_);
                if v_isShared_1099_ == 0 {
                    leanh::lean_ctor_set(v___x_1098_, 0, v___x_1105_);
                    v___x_1107_ = v___x_1098_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
                    v___x_1107_ = v_reuseFailAlloc_1108_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1107_;
            }
            4 => {
                v___x_1114_ = l_Lean_instBEqMVarId_beq(v_x_1087_, v_key_1109_);
                if v___x_1114_ == 0 {
                    leanh::lean_del_object(v___x_1112_);
                    v___x_1115_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1109_,
                        v_val_1110_,
                        v_x_1087_,
                        v_x_1088_,
                    );
                    v___x_1116_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1116_, 0, v___x_1115_);
                    v___y_1104_ = v___x_1116_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1110_);
                    leanh::lean_dec(v_key_1109_);
                    if v_isShared_1113_ == 0 {
                        leanh::lean_ctor_set(v___x_1112_, 1, v_x_1088_);
                        leanh::lean_ctor_set(v___x_1112_, 0, v_x_1087_);
                        v___x_1118_ = v___x_1112_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1119_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_x_1087_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_x_1088_);
                        v___x_1118_ = v_reuseFailAlloc_1119_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1104_ = v___x_1118_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1125_ = lean_usize_shift_right(v_x_1085_, v___x_1090_);
                v___x_1126_ = lean_usize_add(v_x_1086_, v___x_1091_);
                v___x_1127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_node_1121_, v___x_1125_, v___x_1126_, v_x_1087_, v_x_1088_);
                if v_isShared_1124_ == 0 {
                    leanh::lean_ctor_set(v___x_1123_, 0, v___x_1127_);
                    v___x_1129_ = v___x_1123_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1130_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
                    v___x_1129_ = v_reuseFailAlloc_1130_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1104_ = v___x_1129_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1139_ == 0 {
                    v___x_1141_ = v___x_1138_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1155_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_ks_1135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_vs_1136_);
                    v___x_1141_ = v_reuseFailAlloc_1155_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1142_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v___x_1141_, v_x_1087_, v_x_1088_);
                v___x_1150_ = 7usize;
                v___x_1151_ = lean_usize_dec_le(v___x_1150_, v_x_1086_);
                if v___x_1151_ == 0 {
                    v___x_1152_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1142_);
                    v___x_1153_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1154_ = lean_nat_dec_lt(v___x_1152_, v___x_1153_);
                    leanh::lean_dec(v___x_1152_);
                    v___y_1144_ = v___x_1154_;
                    state = 10;
                    continue;
                } else {
                    v___y_1144_ = v___x_1151_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1144_ == 0 {
                    v_ks_1145_ = leanh::lean_ctor_get(v_newNode_1142_, 0);
                    leanh::lean_inc_ref(v_ks_1145_);
                    v_vs_1146_ = leanh::lean_ctor_get(v_newNode_1142_, 1);
                    leanh::lean_inc_ref(v_vs_1146_);
                    leanh::lean_dec_ref(v_newNode_1142_);
                    v___x_1147_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1148_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___closed__2);
                    v___x_1149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_1086_, v_ks_1145_, v_vs_1146_, v___x_1147_, v___x_1148_);
                    leanh::lean_dec_ref(v_vs_1146_);
                    leanh::lean_dec_ref(v_ks_1145_);
                    return v___x_1149_;
                } else {
                    return v_newNode_1142_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_depth_1157_: usize,
    mut v_keys_1158_: *mut leanh::LeanObject,
    mut v_vals_1159_: *mut leanh::LeanObject,
    mut v_i_1160_: *mut leanh::LeanObject,
    mut v_entries_1161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v_k_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u64 = 0;
    let mut v_h_1167_: usize = 0;
    let mut v___x_1168_: usize = 0;
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: usize = 0;
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: usize = 0;
    let mut v_h_1173_: usize = 0;
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1162_ = lean_array_get_size(v_keys_1158_);
                v___x_1163_ = lean_nat_dec_lt(v_i_1160_, v___x_1162_);
                if v___x_1163_ == 0 {
                    leanh::lean_dec(v_i_1160_);
                    return v_entries_1161_;
                } else {
                    v_k_1164_ = lean_array_fget_borrowed(v_keys_1158_, v_i_1160_);
                    v_v_1165_ = lean_array_fget_borrowed(v_vals_1159_, v_i_1160_);
                    v___x_1166_ = l_Lean_instHashableMVarId_hash(v_k_1164_);
                    v_h_1167_ = lean_uint64_to_usize(v___x_1166_);
                    v___x_1168_ = 5usize;
                    v___x_1169_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1170_ = 1usize;
                    v___x_1171_ = lean_usize_sub(v_depth_1157_, v___x_1170_);
                    v___x_1172_ = lean_usize_mul(v___x_1168_, v___x_1171_);
                    v_h_1173_ = lean_usize_shift_right(v_h_1167_, v___x_1172_);
                    v___x_1174_ = lean_nat_add(v_i_1160_, v___x_1169_);
                    leanh::lean_dec(v_i_1160_);
                    leanh::lean_inc(v_v_1165_);
                    leanh::lean_inc(v_k_1164_);
                    v___x_1175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_entries_1161_, v_h_1173_, v_depth_1157_, v_k_1164_, v_v_1165_);
                    v_i_1160_ = v___x_1174_;
                    v_entries_1161_ = v___x_1175_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_depth_1177_: *mut leanh::LeanObject,
    mut v_keys_1178_: *mut leanh::LeanObject,
    mut v_vals_1179_: *mut leanh::LeanObject,
    mut v_i_1180_: *mut leanh::LeanObject,
    mut v_entries_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1182_: usize = 0;
    let mut v_res_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1182_ = leanh::lean_unbox_usize(v_depth_1177_);
    leanh::lean_dec(v_depth_1177_);
    v_res_1183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_boxed_1182_, v_keys_1178_, v_vals_1179_, v_i_1180_, v_entries_1181_);
    leanh::lean_dec_ref(v_vals_1179_);
    leanh::lean_dec_ref(v_keys_1178_);
    return v_res_1183_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_x_1184_: *mut leanh::LeanObject,
    mut v_x_1185_: *mut leanh::LeanObject,
    mut v_x_1186_: *mut leanh::LeanObject,
    mut v_x_1187_: *mut leanh::LeanObject,
    mut v_x_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_9447__boxed_1189_: usize = 0;
    let mut v_x_9448__boxed_1190_: usize = 0;
    let mut v_res_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_9447__boxed_1189_ = leanh::lean_unbox_usize(v_x_1185_);
    leanh::lean_dec(v_x_1185_);
    v_x_9448__boxed_1190_ = leanh::lean_unbox_usize(v_x_1186_);
    leanh::lean_dec(v_x_1186_);
    v_res_1191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_1184_, v_x_9447__boxed_1189_, v_x_9448__boxed_1190_, v_x_1187_, v_x_1188_);
    return v_res_1191_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(
    mut v_x_1192_: *mut leanh::LeanObject,
    mut v_x_1193_: *mut leanh::LeanObject,
    mut v_x_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1195_: u64 = 0;
    let mut v___x_1196_: usize = 0;
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1195_ = l_Lean_instHashableMVarId_hash(v_x_1193_);
    v___x_1196_ = lean_uint64_to_usize(v___x_1195_);
    v___x_1197_ = 1usize;
    v___x_1198_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_1192_, v___x_1196_, v___x_1197_, v_x_1193_, v_x_1194_);
    return v___x_1198_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(
    mut v_mvarId_1199_: *mut leanh::LeanObject,
    mut v_val_1200_: *mut leanh::LeanObject,
    mut v___y_1201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1211_: u8 = 0;
    let mut v_depth_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut v_isSharedCheck_1236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1203_ = lean_st_ref_take(v___y_1201_);
                v_mctx_1204_ = leanh::lean_ctor_get(v___x_1203_, 0);
                v_cache_1205_ = leanh::lean_ctor_get(v___x_1203_, 1);
                v_zetaDeltaFVarIds_1206_ = leanh::lean_ctor_get(v___x_1203_, 2);
                v_postponed_1207_ = leanh::lean_ctor_get(v___x_1203_, 3);
                v_diag_1208_ = leanh::lean_ctor_get(v___x_1203_, 4);
                v_isSharedCheck_1236_ = (!leanh::lean_is_exclusive(v___x_1203_)) as u8;
                if v_isSharedCheck_1236_ == 0 {
                    v___x_1210_ = v___x_1203_;
                    v_isShared_1211_ = v_isSharedCheck_1236_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1208_);
                    leanh::lean_inc(v_postponed_1207_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1206_);
                    leanh::lean_inc(v_cache_1205_);
                    leanh::lean_inc(v_mctx_1204_);
                    leanh::lean_dec(v___x_1203_);
                    v___x_1210_ = leanh::lean_box(0);
                    v_isShared_1211_ = v_isSharedCheck_1236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1212_ = leanh::lean_ctor_get(v_mctx_1204_, 0);
                v_levelAssignDepth_1213_ = leanh::lean_ctor_get(v_mctx_1204_, 1);
                v_lmvarCounter_1214_ = leanh::lean_ctor_get(v_mctx_1204_, 2);
                v_mvarCounter_1215_ = leanh::lean_ctor_get(v_mctx_1204_, 3);
                v_lDecls_1216_ = leanh::lean_ctor_get(v_mctx_1204_, 4);
                v_decls_1217_ = leanh::lean_ctor_get(v_mctx_1204_, 5);
                v_userNames_1218_ = leanh::lean_ctor_get(v_mctx_1204_, 6);
                v_lAssignment_1219_ = leanh::lean_ctor_get(v_mctx_1204_, 7);
                v_eAssignment_1220_ = leanh::lean_ctor_get(v_mctx_1204_, 8);
                v_dAssignment_1221_ = leanh::lean_ctor_get(v_mctx_1204_, 9);
                v_isSharedCheck_1235_ = (!leanh::lean_is_exclusive(v_mctx_1204_)) as u8;
                if v_isSharedCheck_1235_ == 0 {
                    v___x_1223_ = v_mctx_1204_;
                    v_isShared_1224_ = v_isSharedCheck_1235_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1221_);
                    leanh::lean_inc(v_eAssignment_1220_);
                    leanh::lean_inc(v_lAssignment_1219_);
                    leanh::lean_inc(v_userNames_1218_);
                    leanh::lean_inc(v_decls_1217_);
                    leanh::lean_inc(v_lDecls_1216_);
                    leanh::lean_inc(v_mvarCounter_1215_);
                    leanh::lean_inc(v_lmvarCounter_1214_);
                    leanh::lean_inc(v_levelAssignDepth_1213_);
                    leanh::lean_inc(v_depth_1212_);
                    leanh::lean_dec(v_mctx_1204_);
                    v___x_1223_ = leanh::lean_box(0);
                    v_isShared_1224_ = v_isSharedCheck_1235_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1225_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_eAssignment_1220_, v_mvarId_1199_, v_val_1200_);
                if v_isShared_1224_ == 0 {
                    leanh::lean_ctor_set(v___x_1223_, 8, v___x_1225_);
                    v___x_1227_ = v___x_1223_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1234_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_depth_1212_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1234_,
                        1,
                        v_levelAssignDepth_1213_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_lmvarCounter_1214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 3, v_mvarCounter_1215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 4, v_lDecls_1216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 5, v_decls_1217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 6, v_userNames_1218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 7, v_lAssignment_1219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 8, v___x_1225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 9, v_dAssignment_1221_);
                    v___x_1227_ = v_reuseFailAlloc_1234_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1211_ == 0 {
                    leanh::lean_ctor_set(v___x_1210_, 0, v___x_1227_);
                    v___x_1229_ = v___x_1210_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1233_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_cache_1205_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1233_,
                        2,
                        v_zetaDeltaFVarIds_1206_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_postponed_1207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1233_, 4, v_diag_1208_);
                    v___x_1229_ = v_reuseFailAlloc_1233_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1230_ = lean_st_ref_set(v___y_1201_, v___x_1229_);
                v___x_1231_ = leanh::lean_box(0);
                v___x_1232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1232_, 0, v___x_1231_);
                return v___x_1232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg___boxed(
    mut v_mvarId_1237_: *mut leanh::LeanObject,
    mut v_val_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1241_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_1237_, v_val_1238_, v___y_1239_);
    leanh::lean_dec(v___y_1239_);
    return v_res_1241_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3;
    v___x_1253_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__5;
    v___x_1254_ = l_Lean_Name_append(v___x_1253_, v___x_1252_);
    return v___x_1254_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1256_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__7;
    v___x_1257_ = l_Lean_stringToMessageData(v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1270_ = leanh::lean_box(0);
    v___x_1271_ = leanh::lean_unsigned_to_nat(16);
    v___x_1272_ = lean_mk_array(v___x_1271_, v___x_1270_);
    return v___x_1272_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1273_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__13,
    );
    v___x_1274_ = leanh::lean_unsigned_to_nat(0);
    v___x_1275_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1275_, 0, v___x_1274_);
    leanh::lean_ctor_set(v___x_1275_, 1, v___x_1273_);
    return v___x_1275_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1276_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__15,
    );
    v___x_1278_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1278_, 0, v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u8 = 0;
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1279_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16,
    );
    v___x_1280_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__14,
    );
    v___x_1281_ = 1;
    v___x_1282_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_1282_, 0, v___x_1280_);
    leanh::lean_ctor_set(v___x_1282_, 1, v___x_1279_);
    leanh::lean_ctor_set_uint8(
        v___x_1282_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_1281_,
    );
    return v___x_1282_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = leanh::lean_unsigned_to_nat(0);
    v___x_1286_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16,
    );
    v___x_1287_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1287_, 0, v___x_1286_);
    leanh::lean_ctor_set(v___x_1287_, 1, v___x_1285_);
    return v___x_1287_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = leanh::lean_unsigned_to_nat(32);
    v___x_1289_ = lean_mk_empty_array_with_capacity(v___x_1288_);
    v___x_1290_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1290_, 0, v___x_1289_);
    return v___x_1290_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1291_: usize = 0;
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = 5usize;
    v___x_1292_ = leanh::lean_unsigned_to_nat(0);
    v___x_1293_ = leanh::lean_unsigned_to_nat(32);
    v___x_1294_ = lean_mk_empty_array_with_capacity(v___x_1293_);
    v___x_1295_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__20,
    );
    v___x_1296_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1296_, 0, v___x_1295_);
    leanh::lean_ctor_set(v___x_1296_, 1, v___x_1294_);
    leanh::lean_ctor_set(v___x_1296_, 2, v___x_1292_);
    leanh::lean_ctor_set(v___x_1296_, 3, v___x_1292_);
    leanh::lean_ctor_set_usize(v___x_1296_, 4, v___x_1291_);
    return v___x_1296_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__21,
    );
    v___x_1298_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__16,
    );
    v___x_1299_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1299_, 0, v___x_1298_);
    leanh::lean_ctor_set(v___x_1299_, 1, v___x_1298_);
    leanh::lean_ctor_set(v___x_1299_, 2, v___x_1298_);
    leanh::lean_ctor_set(v___x_1299_, 3, v___x_1297_);
    return v___x_1299_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1300_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__22,
    );
    v___x_1301_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19_once
        ),
        _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__19,
    );
    v___x_1302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1302_, 0, v___x_1301_);
    leanh::lean_ctor_set(v___x_1302_, 1, v___x_1300_);
    return v___x_1302_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__29;
    v___x_1314_ = l_Lean_stringToMessageData(v___x_1313_);
    return v___x_1314_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(
    mut v_mvarId_1315_: *mut leanh::LeanObject,
    mut v_h_1316_: *mut leanh::LeanObject,
    mut v_lhs_1317_: *mut leanh::LeanObject,
    mut v_rhs_1318_: *mut leanh::LeanObject,
    mut v_a_1319_: *mut leanh::LeanObject,
    mut v_a_1320_: *mut leanh::LeanObject,
    mut v_a_1321_: *mut leanh::LeanObject,
    mut v_a_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v_a_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut v___y_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v___y_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1359_: u8 = 0;
    let mut v_options_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1362_: u8 = 0;
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: u8 = 0;
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1377_: u8 = 0;
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u8 = 0;
    let mut v___x_1386_: u8 = 0;
    let mut v___y_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1423_: u8 = 0;
    let mut v_fst_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1448_: u8 = 0;
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1470_: u8 = 0;
    let mut v_a_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1390_ =
                    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__11;
                v___x_1391_ = leanh::lean_unsigned_to_nat(1);
                v___x_1392_ = lean_mk_empty_array_with_capacity(v___x_1391_);
                leanh::lean_inc_ref(v___x_1392_);
                v___x_1393_ = lean_array_push(v___x_1392_, v_lhs_1317_);
                v___x_1394_ = l_Lean_Meta_mkAppM(
                    v___x_1390_,
                    v___x_1393_,
                    v_a_1319_,
                    v_a_1320_,
                    v_a_1321_,
                    v_a_1322_,
                );
                if leanh::lean_obj_tag(v___x_1394_) == 0 {
                    v_a_1395_ = leanh::lean_ctor_get(v___x_1394_, 0);
                    leanh::lean_inc(v_a_1395_);
                    leanh::lean_dec_ref_known(v___x_1394_, 1);
                    leanh::lean_inc_ref(v___x_1392_);
                    v___x_1396_ = lean_array_push(v___x_1392_, v_rhs_1318_);
                    v___x_1397_ = l_Lean_Meta_mkAppM(
                        v___x_1390_,
                        v___x_1396_,
                        v_a_1319_,
                        v_a_1320_,
                        v_a_1321_,
                        v_a_1322_,
                    );
                    if leanh::lean_obj_tag(v___x_1397_) == 0 {
                        v_a_1398_ = leanh::lean_ctor_get(v___x_1397_, 0);
                        leanh::lean_inc(v_a_1398_);
                        leanh::lean_dec_ref_known(v___x_1397_, 1);
                        leanh::lean_inc(v_a_1395_);
                        v___x_1399_ = l_Lean_Meta_mkLT(
                            v_a_1395_, v_a_1398_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_,
                        );
                        if leanh::lean_obj_tag(v___x_1399_) == 0 {
                            v_a_1400_ = leanh::lean_ctor_get(v___x_1399_, 0);
                            leanh::lean_inc(v_a_1400_);
                            leanh::lean_dec_ref_known(v___x_1399_, 1);
                            v___x_1401_ = leanh::lean_box(0);
                            v___x_1402_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_a_1400_,
                                v___x_1401_,
                                v_a_1319_,
                                v_a_1320_,
                                v_a_1321_,
                                v_a_1322_,
                            );
                            if leanh::lean_obj_tag(v___x_1402_) == 0 {
                                v_a_1403_ = leanh::lean_ctor_get(v___x_1402_, 0);
                                leanh::lean_inc(v_a_1403_);
                                leanh::lean_dec_ref_known(v___x_1402_, 1);
                                v___x_1404_ = l_Lean_Meta_getSimpTheorems___redArg(v_a_1322_);
                                if leanh::lean_obj_tag(v___x_1404_) == 0 {
                                    v_a_1405_ = leanh::lean_ctor_get(v___x_1404_, 0);
                                    leanh::lean_inc(v_a_1405_);
                                    leanh::lean_dec_ref_known(v___x_1404_, 1);
                                    v___x_1406_ = leanh::lean_unsigned_to_nat(2);
                                    v___x_1407_ = 0;
                                    v___x_1408_ = 1;
                                    v___x_1409_ = leanh::lean_box(0);
                                    v___x_1410_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__12;
                                    leanh::lean_inc_ref(v___x_1392_);
                                    v___x_1411_ = lean_array_push(v___x_1392_, v_a_1405_);
                                    v___x_1412_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17_once), _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__17);
                                    v___x_1413_ = l_Lean_Options_empty;
                                    v___x_1414_ = l_Lean_Meta_Simp_mkContext___redArg(
                                        v___x_1410_,
                                        v___x_1411_,
                                        v___x_1412_,
                                        v___x_1413_,
                                        v_a_1319_,
                                        v_a_1321_,
                                        v_a_1322_,
                                    );
                                    if leanh::lean_obj_tag(v___x_1414_) == 0 {
                                        v_a_1415_ = leanh::lean_ctor_get(v___x_1414_, 0);
                                        leanh::lean_inc(v_a_1415_);
                                        leanh::lean_dec_ref_known(v___x_1414_, 1);
                                        v___x_1416_ = l_Lean_Expr_mvarId_x21(v_a_1403_);
                                        v___x_1417_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__18;
                                        v___x_1418_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23_once), _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__23);
                                        v___x_1419_ = l_Lean_Meta_simpTarget(
                                            v___x_1416_,
                                            v_a_1415_,
                                            v___x_1417_,
                                            v___x_1409_,
                                            v___x_1408_,
                                            v___x_1418_,
                                            v_a_1319_,
                                            v_a_1320_,
                                            v_a_1321_,
                                            v_a_1322_,
                                        );
                                        if leanh::lean_obj_tag(v___x_1419_) == 0 {
                                            v_a_1420_ = leanh::lean_ctor_get(v___x_1419_, 0);
                                            v_isSharedCheck_1470_ =
                                                (!leanh::lean_is_exclusive(v___x_1419_))
                                                    as u8;
                                            if v_isSharedCheck_1470_ == 0 {
                                                v___x_1422_ = v___x_1419_;
                                                v_isShared_1423_ = v_isSharedCheck_1470_;
                                                state = 15;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1420_);
                                                leanh::lean_dec(v___x_1419_);
                                                v___x_1422_ = leanh::lean_box(0);
                                                v_isShared_1423_ = v_isSharedCheck_1470_;
                                                state = 15;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_1403_);
                                            leanh::lean_dec(v_a_1395_);
                                            leanh::lean_dec_ref(v___x_1392_);
                                            leanh::lean_dec_ref(v_h_1316_);
                                            leanh::lean_dec(v_mvarId_1315_);
                                            v_a_1471_ = leanh::lean_ctor_get(v___x_1419_, 0);
                                            leanh::lean_inc(v_a_1471_);
                                            leanh::lean_dec_ref_known(v___x_1419_, 1);
                                            v_a_1384_ = v_a_1471_;
                                            state = 13;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_1403_);
                                        leanh::lean_dec(v_a_1395_);
                                        leanh::lean_dec_ref(v___x_1392_);
                                        leanh::lean_dec_ref(v_h_1316_);
                                        leanh::lean_dec(v_mvarId_1315_);
                                        v_a_1472_ = leanh::lean_ctor_get(v___x_1414_, 0);
                                        leanh::lean_inc(v_a_1472_);
                                        leanh::lean_dec_ref_known(v___x_1414_, 1);
                                        v_a_1384_ = v_a_1472_;
                                        state = 13;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1403_);
                                    leanh::lean_dec(v_a_1395_);
                                    leanh::lean_dec_ref(v___x_1392_);
                                    leanh::lean_dec_ref(v_h_1316_);
                                    leanh::lean_dec(v_mvarId_1315_);
                                    v_a_1473_ = leanh::lean_ctor_get(v___x_1404_, 0);
                                    leanh::lean_inc(v_a_1473_);
                                    leanh::lean_dec_ref_known(v___x_1404_, 1);
                                    v_a_1384_ = v_a_1473_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1395_);
                                leanh::lean_dec_ref(v___x_1392_);
                                leanh::lean_dec_ref(v_h_1316_);
                                leanh::lean_dec(v_mvarId_1315_);
                                v_a_1474_ = leanh::lean_ctor_get(v___x_1402_, 0);
                                leanh::lean_inc(v_a_1474_);
                                leanh::lean_dec_ref_known(v___x_1402_, 1);
                                v_a_1384_ = v_a_1474_;
                                state = 13;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1395_);
                            leanh::lean_dec_ref(v___x_1392_);
                            leanh::lean_dec_ref(v_h_1316_);
                            leanh::lean_dec(v_mvarId_1315_);
                            v_a_1475_ = leanh::lean_ctor_get(v___x_1399_, 0);
                            leanh::lean_inc(v_a_1475_);
                            leanh::lean_dec_ref_known(v___x_1399_, 1);
                            v_a_1384_ = v_a_1475_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1395_);
                        leanh::lean_dec_ref(v___x_1392_);
                        leanh::lean_dec_ref(v_h_1316_);
                        leanh::lean_dec(v_mvarId_1315_);
                        v_a_1476_ = leanh::lean_ctor_get(v___x_1397_, 0);
                        leanh::lean_inc(v_a_1476_);
                        leanh::lean_dec_ref_known(v___x_1397_, 1);
                        v_a_1384_ = v_a_1476_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1392_);
                    leanh::lean_dec_ref(v_rhs_1318_);
                    leanh::lean_dec_ref(v_h_1316_);
                    leanh::lean_dec(v_mvarId_1315_);
                    v_a_1477_ = leanh::lean_ctor_get(v___x_1394_, 0);
                    leanh::lean_inc(v_a_1477_);
                    leanh::lean_dec_ref_known(v___x_1394_, 1);
                    v_a_1384_ = v_a_1477_;
                    state = 13;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1325_) == 0 {
                    v_a_1326_ = leanh::lean_ctor_get(v_a_1325_, 0);
                    v_isSharedCheck_1333_ = (!leanh::lean_is_exclusive(v_a_1325_)) as u8;
                    if v_isSharedCheck_1333_ == 0 {
                        v___x_1328_ = v_a_1325_;
                        v_isShared_1329_ = v_isSharedCheck_1333_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1326_);
                        leanh::lean_dec(v_a_1325_);
                        v___x_1328_ = leanh::lean_box(0);
                        v_isShared_1329_ = v_isSharedCheck_1333_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1334_ = leanh::lean_ctor_get(v_a_1325_, 0);
                    v_isSharedCheck_1341_ = (!leanh::lean_is_exclusive(v_a_1325_)) as u8;
                    if v_isSharedCheck_1341_ == 0 {
                        v___x_1336_ = v_a_1325_;
                        v_isShared_1337_ = v_isSharedCheck_1341_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1334_);
                        leanh::lean_dec(v_a_1325_);
                        v___x_1336_ = leanh::lean_box(0);
                        v_isShared_1337_ = v_isSharedCheck_1341_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1329_ == 0 {
                    v___x_1331_ = v___x_1328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
                    v___x_1331_ = v_reuseFailAlloc_1332_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1331_;
            }
            4 => {
                if v_isShared_1337_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1336_, 0);
                    v___x_1339_ = v___x_1336_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
                    v___x_1339_ = v_reuseFailAlloc_1340_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1339_;
            }
            6 => {
                if leanh::lean_obj_tag(v___y_1343_) == 0 {
                    v_a_1344_ = leanh::lean_ctor_get(v___y_1343_, 0);
                    leanh::lean_inc(v_a_1344_);
                    leanh::lean_dec_ref_known(v___y_1343_, 1);
                    v_a_1325_ = v_a_1344_;
                    state = 1;
                    continue;
                } else {
                    v_a_1345_ = leanh::lean_ctor_get(v___y_1343_, 0);
                    v_isSharedCheck_1352_ = (!leanh::lean_is_exclusive(v___y_1343_)) as u8;
                    if v_isSharedCheck_1352_ == 0 {
                        v___x_1347_ = v___y_1343_;
                        v_isShared_1348_ = v_isSharedCheck_1352_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1345_);
                        leanh::lean_dec(v___y_1343_);
                        v___x_1347_ = leanh::lean_box(0);
                        v_isShared_1348_ = v_isSharedCheck_1352_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1348_ == 0 {
                    v___x_1350_ = v___x_1347_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
                    v___x_1350_ = v_reuseFailAlloc_1351_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1350_;
            }
            9 => {
                v___x_1355_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_1322_);
                leanh::lean_inc_ref(v_a_1321_);
                leanh::lean_inc(v_a_1320_);
                leanh::lean_inc_ref(v_a_1319_);
                v___x_1356_ = leanh::lean_apply_6(
                    v___y_1354_,
                    v___x_1355_,
                    v_a_1319_,
                    v_a_1320_,
                    v_a_1321_,
                    v_a_1322_,
                    leanh::lean_box(0),
                );
                v___y_1343_ = v___x_1356_;
                state = 6;
                continue;
            }
            10 => {
                if v___y_1359_ == 0 {
                    v_options_1360_ = leanh::lean_ctor_get(v_a_1321_, 2);
                    v_inheritedTraceOptions_1361_ = leanh::lean_ctor_get(v_a_1321_, 13);
                    v_hasTrace_1362_ = leanh::lean_ctor_get_uint8(
                        v_options_1360_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_1363_ = leanh::lean_box((v___y_1359_) as usize);
                    v___f_1364_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    leanh::lean_closure_set(v___f_1364_, 0, v___x_1363_);
                    if v_hasTrace_1362_ == 0 {
                        leanh::lean_dec_ref(v___y_1358_);
                        v___y_1354_ = v___f_1364_;
                        state = 9;
                        continue;
                    } else {
                        v___x_1365_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3;
                        v___x_1366_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once), _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
                        v___x_1367_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_1361_,
                            v_options_1360_,
                            v___x_1366_,
                        );
                        if v___x_1367_ == 0 {
                            leanh::lean_dec_ref(v___y_1358_);
                            v___y_1354_ = v___f_1364_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___f_1364_);
                            v___x_1368_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8_once), _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__8);
                            v___x_1369_ = l_Lean_Exception_toMessageData(v___y_1358_);
                            v___x_1370_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1370_, 0, v___x_1368_);
                            leanh::lean_ctor_set(v___x_1370_, 1, v___x_1369_);
                            v___x_1371_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_1365_, v___x_1370_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
                            if leanh::lean_obj_tag(v___x_1371_) == 0 {
                                v_a_1372_ = leanh::lean_ctor_get(v___x_1371_, 0);
                                leanh::lean_inc(v_a_1372_);
                                leanh::lean_dec_ref_known(v___x_1371_, 1);
                                v___x_1373_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__0(v___y_1359_, v_a_1372_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
                                v___y_1343_ = v___x_1373_;
                                state = 6;
                                continue;
                            } else {
                                v_a_1374_ = leanh::lean_ctor_get(v___x_1371_, 0);
                                v_isSharedCheck_1381_ =
                                    (!leanh::lean_is_exclusive(v___x_1371_)) as u8;
                                if v_isSharedCheck_1381_ == 0 {
                                    v___x_1376_ = v___x_1371_;
                                    v_isShared_1377_ = v_isSharedCheck_1381_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1374_);
                                    leanh::lean_dec(v___x_1371_);
                                    v___x_1376_ = leanh::lean_box(0);
                                    v_isShared_1377_ = v_isSharedCheck_1381_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_1382_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1382_, 0, v___y_1358_);
                    return v___x_1382_;
                }
            }
            11 => {
                if v_isShared_1377_ == 0 {
                    v___x_1379_ = v___x_1376_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
                    v___x_1379_ = v_reuseFailAlloc_1380_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1379_;
            }
            13 => {
                v___x_1385_ = l_Lean_Exception_isInterrupt(v_a_1384_);
                if v___x_1385_ == 0 {
                    leanh::lean_inc_ref(v_a_1384_);
                    v___x_1386_ = l_Lean_Exception_isRuntime(v_a_1384_);
                    v___y_1358_ = v_a_1384_;
                    v___y_1359_ = v___x_1386_;
                    state = 10;
                    continue;
                } else {
                    v___y_1358_ = v_a_1384_;
                    v___y_1359_ = v___x_1385_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v_a_1389_ = leanh::lean_ctor_get(v___y_1388_, 0);
                leanh::lean_inc(v_a_1389_);
                leanh::lean_dec_ref(v___y_1388_);
                v_a_1325_ = v_a_1389_;
                state = 1;
                continue;
            }
            15 => {
                v_fst_1424_ = leanh::lean_ctor_get(v_a_1420_, 0);
                leanh::lean_inc(v_fst_1424_);
                leanh::lean_dec(v_a_1420_);
                if leanh::lean_obj_tag(v_fst_1424_) == 0 {
                    leanh::lean_del_object(v___x_1422_);
                    v___x_1425_ =
                        l_Lean_Meta_mkEqSymm(v_h_1316_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
                    if leanh::lean_obj_tag(v___x_1425_) == 0 {
                        v_a_1426_ = leanh::lean_ctor_get(v___x_1425_, 0);
                        leanh::lean_inc(v_a_1426_);
                        leanh::lean_dec_ref_known(v___x_1425_, 1);
                        v___x_1427_ = l_Lean_Expr_appFn_x21(v_a_1395_);
                        v___x_1428_ = l_Lean_Meta_mkCongrArg(
                            v___x_1427_,
                            v_a_1426_,
                            v_a_1319_,
                            v_a_1320_,
                            v_a_1321_,
                            v_a_1322_,
                        );
                        if leanh::lean_obj_tag(v___x_1428_) == 0 {
                            v_a_1429_ = leanh::lean_ctor_get(v___x_1428_, 0);
                            leanh::lean_inc(v_a_1429_);
                            leanh::lean_dec_ref_known(v___x_1428_, 1);
                            v___x_1430_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__26;
                            v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1406_);
                            v___x_1432_ = lean_array_push(v___x_1431_, v_a_1403_);
                            v___x_1433_ = lean_array_push(v___x_1432_, v_a_1429_);
                            v___x_1434_ = l_Lean_Meta_mkAppM(
                                v___x_1430_,
                                v___x_1433_,
                                v_a_1319_,
                                v_a_1320_,
                                v_a_1321_,
                                v_a_1322_,
                            );
                            if leanh::lean_obj_tag(v___x_1434_) == 0 {
                                v_a_1435_ = leanh::lean_ctor_get(v___x_1434_, 0);
                                leanh::lean_inc(v_a_1435_);
                                leanh::lean_dec_ref_known(v___x_1434_, 1);
                                v___x_1436_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__28;
                                v___x_1437_ = lean_array_push(v___x_1392_, v_a_1395_);
                                v___x_1438_ = l_Lean_Meta_mkAppM(
                                    v___x_1436_,
                                    v___x_1437_,
                                    v_a_1319_,
                                    v_a_1320_,
                                    v_a_1321_,
                                    v_a_1322_,
                                );
                                if leanh::lean_obj_tag(v___x_1438_) == 0 {
                                    v_a_1439_ = leanh::lean_ctor_get(v___x_1438_, 0);
                                    leanh::lean_inc(v_a_1439_);
                                    leanh::lean_dec_ref_known(v___x_1438_, 1);
                                    leanh::lean_inc(v_mvarId_1315_);
                                    v___x_1440_ = l_Lean_MVarId_getType(
                                        v_mvarId_1315_,
                                        v_a_1319_,
                                        v_a_1320_,
                                        v_a_1321_,
                                        v_a_1322_,
                                    );
                                    if leanh::lean_obj_tag(v___x_1440_) == 0 {
                                        v_a_1441_ = leanh::lean_ctor_get(v___x_1440_, 0);
                                        leanh::lean_inc(v_a_1441_);
                                        leanh::lean_dec_ref_known(v___x_1440_, 1);
                                        v___x_1442_ =
                                            l_Lean_Expr_app___override(v_a_1439_, v_a_1435_);
                                        v___x_1443_ = l_Lean_Meta_mkFalseElim(
                                            v_a_1441_,
                                            v___x_1442_,
                                            v_a_1319_,
                                            v_a_1320_,
                                            v_a_1321_,
                                            v_a_1322_,
                                        );
                                        if leanh::lean_obj_tag(v___x_1443_) == 0 {
                                            v_a_1444_ = leanh::lean_ctor_get(v___x_1443_, 0);
                                            leanh::lean_inc(v_a_1444_);
                                            leanh::lean_dec_ref_known(v___x_1443_, 1);
                                            v___x_1445_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_1315_, v_a_1444_, v_a_1320_);
                                            leanh::lean_dec_ref(v___x_1445_);
                                            v_options_1446_ =
                                                leanh::lean_ctor_get(v_a_1321_, 2);
                                            v_inheritedTraceOptions_1447_ =
                                                leanh::lean_ctor_get(v_a_1321_, 13);
                                            v_hasTrace_1448_ = leanh::lean_ctor_get_uint8(
                                                v_options_1446_,
                                                (core::mem::size_of::<*mut leanh::LeanObject>(
                                                ) * 1)
                                                    as u32,
                                            );
                                            if v_hasTrace_1448_ == 0 {
                                                state = 16;
                                                continue;
                                            } else {
                                                v___x_1452_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3;
                                                v___x_1453_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once), _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
                                                v___x_1454_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1447_, v_options_1446_, v___x_1453_);
                                                if v___x_1454_ == 0 {
                                                    state = 16;
                                                    continue;
                                                } else {
                                                    v___x_1455_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30_once), _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__30);
                                                    v___x_1456_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_1452_, v___x_1455_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
                                                    if leanh::lean_obj_tag(v___x_1456_) == 0
                                                    {
                                                        v_a_1457_ = leanh::lean_ctor_get(
                                                            v___x_1456_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_1457_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_1456_,
                                                            1,
                                                        );
                                                        v___x_1458_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(v___x_1408_, v_a_1457_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
                                                        v___y_1388_ = v___x_1458_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        v_a_1459_ = leanh::lean_ctor_get(
                                                            v___x_1456_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_a_1459_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_1456_,
                                                            1,
                                                        );
                                                        v_a_1384_ = v_a_1459_;
                                                        state = 13;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_mvarId_1315_);
                                            v_a_1460_ = leanh::lean_ctor_get(v___x_1443_, 0);
                                            leanh::lean_inc(v_a_1460_);
                                            leanh::lean_dec_ref_known(v___x_1443_, 1);
                                            v_a_1384_ = v_a_1460_;
                                            state = 13;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_1439_);
                                        leanh::lean_dec(v_a_1435_);
                                        leanh::lean_dec(v_mvarId_1315_);
                                        v_a_1461_ = leanh::lean_ctor_get(v___x_1440_, 0);
                                        leanh::lean_inc(v_a_1461_);
                                        leanh::lean_dec_ref_known(v___x_1440_, 1);
                                        v_a_1384_ = v_a_1461_;
                                        state = 13;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1435_);
                                    leanh::lean_dec(v_mvarId_1315_);
                                    v_a_1462_ = leanh::lean_ctor_get(v___x_1438_, 0);
                                    leanh::lean_inc(v_a_1462_);
                                    leanh::lean_dec_ref_known(v___x_1438_, 1);
                                    v_a_1384_ = v_a_1462_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1395_);
                                leanh::lean_dec_ref(v___x_1392_);
                                leanh::lean_dec(v_mvarId_1315_);
                                v_a_1463_ = leanh::lean_ctor_get(v___x_1434_, 0);
                                leanh::lean_inc(v_a_1463_);
                                leanh::lean_dec_ref_known(v___x_1434_, 1);
                                v_a_1384_ = v_a_1463_;
                                state = 13;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1403_);
                            leanh::lean_dec(v_a_1395_);
                            leanh::lean_dec_ref(v___x_1392_);
                            leanh::lean_dec(v_mvarId_1315_);
                            v_a_1464_ = leanh::lean_ctor_get(v___x_1428_, 0);
                            leanh::lean_inc(v_a_1464_);
                            leanh::lean_dec_ref_known(v___x_1428_, 1);
                            v_a_1384_ = v_a_1464_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1403_);
                        leanh::lean_dec(v_a_1395_);
                        leanh::lean_dec_ref(v___x_1392_);
                        leanh::lean_dec(v_mvarId_1315_);
                        v_a_1465_ = leanh::lean_ctor_get(v___x_1425_, 0);
                        leanh::lean_inc(v_a_1465_);
                        leanh::lean_dec_ref_known(v___x_1425_, 1);
                        v_a_1384_ = v_a_1465_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_fst_1424_, 1);
                    leanh::lean_dec(v_a_1403_);
                    leanh::lean_dec(v_a_1395_);
                    leanh::lean_dec_ref(v___x_1392_);
                    leanh::lean_dec_ref(v_h_1316_);
                    leanh::lean_dec(v_mvarId_1315_);
                    v___x_1466_ = leanh::lean_box((v___x_1407_) as usize);
                    if v_isShared_1423_ == 0 {
                        leanh::lean_ctor_set(v___x_1422_, 0, v___x_1466_);
                        v___x_1468_ = v___x_1422_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
                        v___x_1468_ = v_reuseFailAlloc_1469_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                v___x_1450_ = leanh::lean_box(0);
                v___x_1451_ =
                    l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___lam__1(
                        v___x_1408_,
                        v___x_1450_,
                        v_a_1319_,
                        v_a_1320_,
                        v_a_1321_,
                        v_a_1322_,
                    );
                v___y_1388_ = v___x_1451_;
                state = 14;
                continue;
            }
            17 => {
                return v___x_1468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___boxed(
    mut v_mvarId_1478_: *mut leanh::LeanObject,
    mut v_h_1479_: *mut leanh::LeanObject,
    mut v_lhs_1480_: *mut leanh::LeanObject,
    mut v_rhs_1481_: *mut leanh::LeanObject,
    mut v_a_1482_: *mut leanh::LeanObject,
    mut v_a_1483_: *mut leanh::LeanObject,
    mut v_a_1484_: *mut leanh::LeanObject,
    mut v_a_1485_: *mut leanh::LeanObject,
    mut v_a_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1487_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(
        v_mvarId_1478_,
        v_h_1479_,
        v_lhs_1480_,
        v_rhs_1481_,
        v_a_1482_,
        v_a_1483_,
        v_a_1484_,
        v_a_1485_,
    );
    leanh::lean_dec(v_a_1485_);
    leanh::lean_dec_ref(v_a_1484_);
    leanh::lean_dec(v_a_1483_);
    leanh::lean_dec_ref(v_a_1482_);
    return v_res_1487_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(
    mut v_mvarId_1488_: *mut leanh::LeanObject,
    mut v_val_1489_: *mut leanh::LeanObject,
    mut v___y_1490_: *mut leanh::LeanObject,
    mut v___y_1491_: *mut leanh::LeanObject,
    mut v___y_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___redArg(v_mvarId_1488_, v_val_1489_, v___y_1491_);
    return v___x_1495_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1___boxed(
    mut v_mvarId_1496_: *mut leanh::LeanObject,
    mut v_val_1497_: *mut leanh::LeanObject,
    mut v___y_1498_: *mut leanh::LeanObject,
    mut v___y_1499_: *mut leanh::LeanObject,
    mut v___y_1500_: *mut leanh::LeanObject,
    mut v___y_1501_: *mut leanh::LeanObject,
    mut v___y_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1503_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1(v_mvarId_1496_, v_val_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
    leanh::lean_dec(v___y_1501_);
    leanh::lean_dec_ref(v___y_1500_);
    leanh::lean_dec(v___y_1499_);
    leanh::lean_dec_ref(v___y_1498_);
    return v_res_1503_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2(
    mut v_00_u03b2_1504_: *mut leanh::LeanObject,
    mut v_x_1505_: *mut leanh::LeanObject,
    mut v_x_1506_: *mut leanh::LeanObject,
    mut v_x_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1508_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2___redArg(v_x_1505_, v_x_1506_, v_x_1507_);
    return v___x_1508_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(
    mut v_00_u03b2_1509_: *mut leanh::LeanObject,
    mut v_x_1510_: *mut leanh::LeanObject,
    mut v_x_1511_: usize,
    mut v_x_1512_: usize,
    mut v_x_1513_: *mut leanh::LeanObject,
    mut v_x_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___redArg(v_x_1510_, v_x_1511_, v_x_1512_, v_x_1513_, v_x_1514_);
    return v___x_1515_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_1516_: *mut leanh::LeanObject,
    mut v_x_1517_: *mut leanh::LeanObject,
    mut v_x_1518_: *mut leanh::LeanObject,
    mut v_x_1519_: *mut leanh::LeanObject,
    mut v_x_1520_: *mut leanh::LeanObject,
    mut v_x_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_10282__boxed_1522_: usize = 0;
    let mut v_x_10283__boxed_1523_: usize = 0;
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_10282__boxed_1522_ = leanh::lean_unbox_usize(v_x_1518_);
    leanh::lean_dec(v_x_1518_);
    v_x_10283__boxed_1523_ = leanh::lean_unbox_usize(v_x_1519_);
    leanh::lean_dec(v_x_1519_);
    v_res_1524_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3(v_00_u03b2_1516_, v_x_1517_, v_x_10282__boxed_1522_, v_x_10283__boxed_1523_, v_x_1520_, v_x_1521_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1525_: *mut leanh::LeanObject,
    mut v_n_1526_: *mut leanh::LeanObject,
    mut v_k_1527_: *mut leanh::LeanObject,
    mut v_v_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4___redArg(v_n_1526_, v_k_1527_, v_v_1528_);
    return v___x_1529_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1530_: *mut leanh::LeanObject,
    mut v_depth_1531_: usize,
    mut v_keys_1532_: *mut leanh::LeanObject,
    mut v_vals_1533_: *mut leanh::LeanObject,
    mut v_heq_1534_: *mut leanh::LeanObject,
    mut v_i_1535_: *mut leanh::LeanObject,
    mut v_entries_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___redArg(v_depth_1531_, v_keys_1532_, v_vals_1533_, v_i_1535_, v_entries_1536_);
    return v___x_1537_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b2_1538_: *mut leanh::LeanObject,
    mut v_depth_1539_: *mut leanh::LeanObject,
    mut v_keys_1540_: *mut leanh::LeanObject,
    mut v_vals_1541_: *mut leanh::LeanObject,
    mut v_heq_1542_: *mut leanh::LeanObject,
    mut v_i_1543_: *mut leanh::LeanObject,
    mut v_entries_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1545_: usize = 0;
    let mut v_res_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1545_ = leanh::lean_unbox_usize(v_depth_1539_);
    leanh::lean_dec(v_depth_1539_);
    v_res_1546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__5(v_00_u03b2_1538_, v_depth_boxed_1545_, v_keys_1540_, v_vals_1541_, v_heq_1542_, v_i_1543_, v_entries_1544_);
    leanh::lean_dec_ref(v_vals_1541_);
    leanh::lean_dec_ref(v_keys_1540_);
    return v_res_1546_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1547_: *mut leanh::LeanObject,
    mut v_x_1548_: *mut leanh::LeanObject,
    mut v_x_1549_: *mut leanh::LeanObject,
    mut v_x_1550_: *mut leanh::LeanObject,
    mut v_x_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_x_1548_, v_x_1549_, v_x_1550_, v_x_1551_);
    return v___x_1552_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(
    mut v_mvarId_1553_: *mut leanh::LeanObject,
    mut v_x_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
    mut v___y_1556_: *mut leanh::LeanObject,
    mut v___y_1557_: *mut leanh::LeanObject,
    mut v___y_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v_a_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1572_: u8 = 0;
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1560_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1553_,
                    v_x_1554_,
                    v___y_1555_,
                    v___y_1556_,
                    v___y_1557_,
                    v___y_1558_,
                );
                if leanh::lean_obj_tag(v___x_1560_) == 0 {
                    v_a_1561_ = leanh::lean_ctor_get(v___x_1560_, 0);
                    v_isSharedCheck_1568_ = (!leanh::lean_is_exclusive(v___x_1560_)) as u8;
                    if v_isSharedCheck_1568_ == 0 {
                        v___x_1563_ = v___x_1560_;
                        v_isShared_1564_ = v_isSharedCheck_1568_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1561_);
                        leanh::lean_dec(v___x_1560_);
                        v___x_1563_ = leanh::lean_box(0);
                        v_isShared_1564_ = v_isSharedCheck_1568_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1569_ = leanh::lean_ctor_get(v___x_1560_, 0);
                    v_isSharedCheck_1576_ = (!leanh::lean_is_exclusive(v___x_1560_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v___x_1571_ = v___x_1560_;
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1569_);
                        leanh::lean_dec(v___x_1560_);
                        v___x_1571_ = leanh::lean_box(0);
                        v_isShared_1572_ = v_isSharedCheck_1576_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1564_ == 0 {
                    v___x_1566_ = v___x_1563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
                    v___x_1566_ = v_reuseFailAlloc_1567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1566_;
            }
            3 => {
                if v_isShared_1572_ == 0 {
                    v___x_1574_ = v___x_1571_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
                    v___x_1574_ = v_reuseFailAlloc_1575_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg___boxed(
    mut v_mvarId_1577_: *mut leanh::LeanObject,
    mut v_x_1578_: *mut leanh::LeanObject,
    mut v___y_1579_: *mut leanh::LeanObject,
    mut v___y_1580_: *mut leanh::LeanObject,
    mut v___y_1581_: *mut leanh::LeanObject,
    mut v___y_1582_: *mut leanh::LeanObject,
    mut v___y_1583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(
        v_mvarId_1577_,
        v_x_1578_,
        v___y_1579_,
        v___y_1580_,
        v___y_1581_,
        v___y_1582_,
    );
    leanh::lean_dec(v___y_1582_);
    leanh::lean_dec_ref(v___y_1581_);
    leanh::lean_dec(v___y_1580_);
    leanh::lean_dec_ref(v___y_1579_);
    return v_res_1584_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(
    mut v_00_u03b1_1585_: *mut leanh::LeanObject,
    mut v_mvarId_1586_: *mut leanh::LeanObject,
    mut v_x_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
    mut v___y_1590_: *mut leanh::LeanObject,
    mut v___y_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(
        v_mvarId_1586_,
        v_x_1587_,
        v___y_1588_,
        v___y_1589_,
        v___y_1590_,
        v___y_1591_,
    );
    return v___x_1593_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___boxed(
    mut v_00_u03b1_1594_: *mut leanh::LeanObject,
    mut v_mvarId_1595_: *mut leanh::LeanObject,
    mut v_x_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
    mut v___y_1601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0(
        v_00_u03b1_1594_,
        v_mvarId_1595_,
        v_x_1596_,
        v___y_1597_,
        v___y_1598_,
        v___y_1599_,
        v___y_1600_,
    );
    leanh::lean_dec(v___y_1600_);
    leanh::lean_dec_ref(v___y_1599_);
    leanh::lean_dec(v___y_1598_);
    leanh::lean_dec_ref(v___y_1597_);
    return v_res_1602_;
}
pub unsafe fn _init_l_Lean_MVarId_acyclic___lam__0___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = l_Lean_MVarId_acyclic___lam__0___closed__2;
    v___x_1608_ = l_Lean_stringToMessageData(v___x_1607_);
    return v___x_1608_;
}
pub unsafe fn l_Lean_MVarId_acyclic___lam__0(
    mut v_h_1609_: *mut leanh::LeanObject,
    mut v_mvarId_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
    mut v___y_1614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1622_: u8 = 0;
    let mut v___y_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: u8 = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1650_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1654_: u8 = 0;
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1657_: u8 = 0;
    let mut v_inheritedTraceOptions_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1669_: u8 = 0;
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1673_: u8 = 0;
    let mut v_isSharedCheck_1674_: u8 = 0;
    let mut v_a_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1682_: u8 = 0;
    let mut v_a_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1690_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1614_);
                leanh::lean_inc_ref(v___y_1613_);
                leanh::lean_inc(v___y_1612_);
                leanh::lean_inc_ref(v___y_1611_);
                leanh::lean_inc_ref(v_h_1609_);
                v___x_1616_ = lean_infer_type(
                    v_h_1609_,
                    v___y_1611_,
                    v___y_1612_,
                    v___y_1613_,
                    v___y_1614_,
                );
                if leanh::lean_obj_tag(v___x_1616_) == 0 {
                    v_a_1617_ = leanh::lean_ctor_get(v___x_1616_, 0);
                    leanh::lean_inc(v_a_1617_);
                    leanh::lean_dec_ref_known(v___x_1616_, 1);
                    v___x_1618_ = l_Lean_Meta_whnfD(
                        v_a_1617_,
                        v___y_1611_,
                        v___y_1612_,
                        v___y_1613_,
                        v___y_1614_,
                    );
                    if leanh::lean_obj_tag(v___x_1618_) == 0 {
                        v_a_1619_ = leanh::lean_ctor_get(v___x_1618_, 0);
                        v_isSharedCheck_1674_ =
                            (!leanh::lean_is_exclusive(v___x_1618_)) as u8;
                        if v_isSharedCheck_1674_ == 0 {
                            v___x_1621_ = v___x_1618_;
                            v_isShared_1622_ = v_isSharedCheck_1674_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1619_);
                            leanh::lean_dec(v___x_1618_);
                            v___x_1621_ = leanh::lean_box(0);
                            v_isShared_1622_ = v_isSharedCheck_1674_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_1614_);
                        leanh::lean_dec_ref(v___y_1613_);
                        leanh::lean_dec(v___y_1612_);
                        leanh::lean_dec_ref(v___y_1611_);
                        leanh::lean_dec(v_mvarId_1610_);
                        leanh::lean_dec_ref(v_h_1609_);
                        v_a_1675_ = leanh::lean_ctor_get(v___x_1618_, 0);
                        v_isSharedCheck_1682_ =
                            (!leanh::lean_is_exclusive(v___x_1618_)) as u8;
                        if v_isSharedCheck_1682_ == 0 {
                            v___x_1677_ = v___x_1618_;
                            v_isShared_1678_ = v_isSharedCheck_1682_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1675_);
                            leanh::lean_dec(v___x_1618_);
                            v___x_1677_ = leanh::lean_box(0);
                            v_isShared_1678_ = v_isSharedCheck_1682_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_1614_);
                    leanh::lean_dec_ref(v___y_1613_);
                    leanh::lean_dec(v___y_1612_);
                    leanh::lean_dec_ref(v___y_1611_);
                    leanh::lean_dec(v_mvarId_1610_);
                    leanh::lean_dec_ref(v_h_1609_);
                    v_a_1683_ = leanh::lean_ctor_get(v___x_1616_, 0);
                    v_isSharedCheck_1690_ = (!leanh::lean_is_exclusive(v___x_1616_)) as u8;
                    if v_isSharedCheck_1690_ == 0 {
                        v___x_1685_ = v___x_1616_;
                        v_isShared_1686_ = v_isSharedCheck_1690_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1683_);
                        leanh::lean_dec(v___x_1616_);
                        v___x_1685_ = leanh::lean_box(0);
                        v_isShared_1686_ = v_isSharedCheck_1690_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_options_1656_ = leanh::lean_ctor_get(v___y_1613_, 2);
                v_hasTrace_1657_ = leanh::lean_ctor_get_uint8(
                    v_options_1656_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_1657_ == 0 {
                    v___y_1624_ = v___y_1611_;
                    v___y_1625_ = v___y_1612_;
                    v___y_1626_ = v___y_1613_;
                    v___y_1627_ = v___y_1614_;
                    state = 2;
                    continue;
                } else {
                    v_inheritedTraceOptions_1658_ = leanh::lean_ctor_get(v___y_1613_, 13);
                    v___x_1659_ =
                        l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3;
                    v___x_1660_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6_once), _init_l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__6);
                    v___x_1661_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_1658_,
                        v_options_1656_,
                        v___x_1660_,
                    );
                    if v___x_1661_ == 0 {
                        v___y_1624_ = v___y_1611_;
                        v___y_1625_ = v___y_1612_;
                        v___y_1626_ = v___y_1613_;
                        v___y_1627_ = v___y_1614_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1662_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_acyclic___lam__0___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_acyclic___lam__0___closed__3_once
                            ),
                            _init_l_Lean_MVarId_acyclic___lam__0___closed__3,
                        );
                        leanh::lean_inc(v_a_1619_);
                        v___x_1663_ = l_Lean_MessageData_ofExpr(v_a_1619_);
                        v___x_1664_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1664_, 0, v___x_1662_);
                        leanh::lean_ctor_set(v___x_1664_, 1, v___x_1663_);
                        v___x_1665_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go_spec__0(v___x_1659_, v___x_1664_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
                        if leanh::lean_obj_tag(v___x_1665_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1665_, 1);
                            v___y_1624_ = v___y_1611_;
                            v___y_1625_ = v___y_1612_;
                            v___y_1626_ = v___y_1613_;
                            v___y_1627_ = v___y_1614_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_1621_);
                            leanh::lean_dec(v_a_1619_);
                            leanh::lean_dec(v___y_1614_);
                            leanh::lean_dec_ref(v___y_1613_);
                            leanh::lean_dec(v___y_1612_);
                            leanh::lean_dec_ref(v___y_1611_);
                            leanh::lean_dec(v_mvarId_1610_);
                            leanh::lean_dec_ref(v_h_1609_);
                            v_a_1666_ = leanh::lean_ctor_get(v___x_1665_, 0);
                            v_isSharedCheck_1673_ =
                                (!leanh::lean_is_exclusive(v___x_1665_)) as u8;
                            if v_isSharedCheck_1673_ == 0 {
                                v___x_1668_ = v___x_1665_;
                                v_isShared_1669_ = v_isSharedCheck_1673_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1666_);
                                leanh::lean_dec(v___x_1665_);
                                v___x_1668_ = leanh::lean_box(0);
                                v_isShared_1669_ = v_isSharedCheck_1673_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1628_ = l_Lean_MVarId_acyclic___lam__0___closed__1;
                v___x_1629_ = leanh::lean_unsigned_to_nat(3);
                v___x_1630_ = l_Lean_Expr_isAppOfArity(v_a_1619_, v___x_1628_, v___x_1629_);
                if v___x_1630_ == 0 {
                    leanh::lean_dec(v___y_1627_);
                    leanh::lean_dec_ref(v___y_1626_);
                    leanh::lean_dec(v___y_1625_);
                    leanh::lean_dec_ref(v___y_1624_);
                    leanh::lean_dec(v_a_1619_);
                    leanh::lean_dec(v_mvarId_1610_);
                    leanh::lean_dec_ref(v_h_1609_);
                    v___x_1631_ = leanh::lean_box((v___x_1630_) as usize);
                    if v_isShared_1622_ == 0 {
                        leanh::lean_ctor_set(v___x_1621_, 0, v___x_1631_);
                        v___x_1633_ = v___x_1621_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1634_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
                        v___x_1633_ = v_reuseFailAlloc_1634_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1621_);
                    v___x_1635_ = l_Lean_Expr_appFn_x21(v_a_1619_);
                    v___x_1636_ = l_Lean_Expr_appArg_x21(v___x_1635_);
                    leanh::lean_dec_ref(v___x_1635_);
                    v___x_1637_ = l_Lean_Expr_appArg_x21(v_a_1619_);
                    leanh::lean_dec(v_a_1619_);
                    leanh::lean_inc_ref(v___x_1637_);
                    leanh::lean_inc_ref(v___x_1636_);
                    v___x_1638_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(
                        v___x_1636_,
                        v___x_1637_,
                        v___y_1624_,
                        v___y_1625_,
                        v___y_1626_,
                        v___y_1627_,
                    );
                    if leanh::lean_obj_tag(v___x_1638_) == 0 {
                        v_a_1639_ = leanh::lean_ctor_get(v___x_1638_, 0);
                        leanh::lean_inc(v_a_1639_);
                        leanh::lean_dec_ref_known(v___x_1638_, 1);
                        v___x_1640_ = (leanh::lean_unbox(v_a_1639_) as u8);
                        leanh::lean_dec(v_a_1639_);
                        if v___x_1640_ == 0 {
                            leanh::lean_inc_ref(v___x_1636_);
                            leanh::lean_inc_ref(v___x_1637_);
                            v___x_1641_ =
                                l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(
                                    v___x_1637_,
                                    v___x_1636_,
                                    v___y_1624_,
                                    v___y_1625_,
                                    v___y_1626_,
                                    v___y_1627_,
                                );
                            if leanh::lean_obj_tag(v___x_1641_) == 0 {
                                v_a_1642_ = leanh::lean_ctor_get(v___x_1641_, 0);
                                leanh::lean_inc(v_a_1642_);
                                v___x_1643_ = (leanh::lean_unbox(v_a_1642_) as u8);
                                leanh::lean_dec(v_a_1642_);
                                if v___x_1643_ == 0 {
                                    leanh::lean_dec_ref(v___x_1637_);
                                    leanh::lean_dec_ref(v___x_1636_);
                                    leanh::lean_dec(v___y_1627_);
                                    leanh::lean_dec_ref(v___y_1626_);
                                    leanh::lean_dec(v___y_1625_);
                                    leanh::lean_dec_ref(v___y_1624_);
                                    leanh::lean_dec(v_mvarId_1610_);
                                    leanh::lean_dec_ref(v_h_1609_);
                                    return v___x_1641_;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_1641_, 1);
                                    v___x_1644_ = l_Lean_Meta_mkEqSymm(
                                        v_h_1609_,
                                        v___y_1624_,
                                        v___y_1625_,
                                        v___y_1626_,
                                        v___y_1627_,
                                    );
                                    if leanh::lean_obj_tag(v___x_1644_) == 0 {
                                        v_a_1645_ = leanh::lean_ctor_get(v___x_1644_, 0);
                                        leanh::lean_inc(v_a_1645_);
                                        leanh::lean_dec_ref_known(v___x_1644_, 1);
                                        v___x_1646_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(v_mvarId_1610_, v_a_1645_, v___x_1637_, v___x_1636_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
                                        leanh::lean_dec(v___y_1627_);
                                        leanh::lean_dec_ref(v___y_1626_);
                                        leanh::lean_dec(v___y_1625_);
                                        leanh::lean_dec_ref(v___y_1624_);
                                        return v___x_1646_;
                                    } else {
                                        leanh::lean_dec_ref(v___x_1637_);
                                        leanh::lean_dec_ref(v___x_1636_);
                                        leanh::lean_dec(v___y_1627_);
                                        leanh::lean_dec_ref(v___y_1626_);
                                        leanh::lean_dec(v___y_1625_);
                                        leanh::lean_dec_ref(v___y_1624_);
                                        leanh::lean_dec(v_mvarId_1610_);
                                        v_a_1647_ = leanh::lean_ctor_get(v___x_1644_, 0);
                                        v_isSharedCheck_1654_ =
                                            (!leanh::lean_is_exclusive(v___x_1644_)) as u8;
                                        if v_isSharedCheck_1654_ == 0 {
                                            v___x_1649_ = v___x_1644_;
                                            v_isShared_1650_ = v_isSharedCheck_1654_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1647_);
                                            leanh::lean_dec(v___x_1644_);
                                            v___x_1649_ = leanh::lean_box(0);
                                            v_isShared_1650_ = v_isSharedCheck_1654_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_1637_);
                                leanh::lean_dec_ref(v___x_1636_);
                                leanh::lean_dec(v___y_1627_);
                                leanh::lean_dec_ref(v___y_1626_);
                                leanh::lean_dec(v___y_1625_);
                                leanh::lean_dec_ref(v___y_1624_);
                                leanh::lean_dec(v_mvarId_1610_);
                                leanh::lean_dec_ref(v_h_1609_);
                                return v___x_1641_;
                            }
                        } else {
                            v___x_1655_ =
                                l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go(
                                    v_mvarId_1610_,
                                    v_h_1609_,
                                    v___x_1636_,
                                    v___x_1637_,
                                    v___y_1624_,
                                    v___y_1625_,
                                    v___y_1626_,
                                    v___y_1627_,
                                );
                            leanh::lean_dec(v___y_1627_);
                            leanh::lean_dec_ref(v___y_1626_);
                            leanh::lean_dec(v___y_1625_);
                            leanh::lean_dec_ref(v___y_1624_);
                            return v___x_1655_;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1637_);
                        leanh::lean_dec_ref(v___x_1636_);
                        leanh::lean_dec(v___y_1627_);
                        leanh::lean_dec_ref(v___y_1626_);
                        leanh::lean_dec(v___y_1625_);
                        leanh::lean_dec_ref(v___y_1624_);
                        leanh::lean_dec(v_mvarId_1610_);
                        leanh::lean_dec_ref(v_h_1609_);
                        return v___x_1638_;
                    }
                }
            }
            3 => {
                return v___x_1633_;
            }
            4 => {
                if v_isShared_1650_ == 0 {
                    v___x_1652_ = v___x_1649_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
                    v___x_1652_ = v_reuseFailAlloc_1653_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1652_;
            }
            6 => {
                if v_isShared_1669_ == 0 {
                    v___x_1671_ = v___x_1668_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1672_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
                    v___x_1671_ = v_reuseFailAlloc_1672_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1671_;
            }
            8 => {
                if v_isShared_1678_ == 0 {
                    v___x_1680_ = v___x_1677_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1681_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
                    v___x_1680_ = v_reuseFailAlloc_1681_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1680_;
            }
            10 => {
                if v_isShared_1686_ == 0 {
                    v___x_1688_ = v___x_1685_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1689_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
                    v___x_1688_ = v_reuseFailAlloc_1689_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_acyclic___lam__0___boxed(
    mut v_h_1691_: *mut leanh::LeanObject,
    mut v_mvarId_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1698_ = l_Lean_MVarId_acyclic___lam__0(
        v_h_1691_,
        v_mvarId_1692_,
        v___y_1693_,
        v___y_1694_,
        v___y_1695_,
        v___y_1696_,
    );
    return v_res_1698_;
}
pub unsafe fn l_Lean_MVarId_acyclic(
    mut v_mvarId_1699_: *mut leanh::LeanObject,
    mut v_h_1700_: *mut leanh::LeanObject,
    mut v_a_1701_: *mut leanh::LeanObject,
    mut v_a_1702_: *mut leanh::LeanObject,
    mut v_a_1703_: *mut leanh::LeanObject,
    mut v_a_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_1699_);
    v___f_1706_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_acyclic___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_1706_, 0, v_h_1700_);
    leanh::lean_closure_set(v___f_1706_, 1, v_mvarId_1699_);
    v___x_1707_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_acyclic_spec__0___redArg(
        v_mvarId_1699_,
        v___f_1706_,
        v_a_1701_,
        v_a_1702_,
        v_a_1703_,
        v_a_1704_,
    );
    return v___x_1707_;
}
pub unsafe fn l_Lean_MVarId_acyclic___boxed(
    mut v_mvarId_1708_: *mut leanh::LeanObject,
    mut v_h_1709_: *mut leanh::LeanObject,
    mut v_a_1710_: *mut leanh::LeanObject,
    mut v_a_1711_: *mut leanh::LeanObject,
    mut v_a_1712_: *mut leanh::LeanObject,
    mut v_a_1713_: *mut leanh::LeanObject,
    mut v_a_1714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ = l_Lean_MVarId_acyclic(
        v_mvarId_1708_,
        v_h_1709_,
        v_a_1710_,
        v_a_1711_,
        v_a_1712_,
        v_a_1713_,
    );
    leanh::lean_dec(v_a_1713_);
    leanh::lean_dec_ref(v_a_1712_);
    leanh::lean_dec(v_a_1711_);
    leanh::lean_dec_ref(v_a_1710_);
    return v_res_1715_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1779_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_acyclic_go___closed__3;
    v___x_1780_ = 0;
    v___x_1781_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn___closed__25_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_;
    v___x_1782_ = l_Lean_registerTraceClass(v___x_1779_, v___x_1780_, v___x_1781_);
    return v___x_1782_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2____boxed(
    mut v_a_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1784_ = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
    return v_res_1784_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Acyclic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_initFn_00___x40_Lean_Meta_Tactic_Acyclic_1360063758____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Acyclic(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Acyclic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_MatchUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Acyclic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Acyclic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Acyclic(builtin);
}