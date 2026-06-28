// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.Types Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM Lean.Meta.Tactic.Grind.Arith.CommRing.Functions Lean.Meta.Tactic.Grind.Arith.CommRing.Reify Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr Lean.Meta.Tactic.Grind.Arith.CommRing.Proof Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Lean.Meta.Tactic.Grind.Arith.CommRing.Inv Lean.Meta.Tactic.Grind.Arith.CommRing.PP Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing Lean.Meta.Tactic.Grind.Arith.CommRing.MonadSemiring Lean.Meta.Tactic.Grind.Arith.CommRing.Action Lean.Meta.Tactic.Grind.Arith.CommRing.Power
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Action::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action, l_Lean_Meta_Grind_Action_ring___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::EqCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr,
    l_Lean_Meta_Grind_Arith_CommRing_check_x27___boxed,
    l_Lean_Meta_Grind_Arith_CommRing_processNewDiseq___boxed,
    l_Lean_Meta_Grind_Arith_CommRing_processNewEq___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Functions::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Internalize::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize,
    l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Inv::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv,
    l_Lean_Meta_Grind_Arith_CommRing_checkInvariants___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::MonadRing::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::MonadSemiring::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::NonCommRingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::NonCommSemiringM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::PP::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Power::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Proof::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Reify::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::SemiringM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
    l_Lean_Meta_Grind_Arith_CommRing_ringExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_SolverExtension_setMethods___redArg;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,622053547050603573 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7655114909728474417 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 109, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14785409762281932364 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,12833161325241227853 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15948583408990530872 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16046516903769087636 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12688987844954821806 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1628631271144195566 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11403964697897510527 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6647257981682712606 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6727373836467124671 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14503154075155024370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2181067493093289894 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1060138090082246139 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15880579792917111949 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8204911064715934137 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5774094994212982820 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13114681713692780684 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7745963705971466163 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [117, 110, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7745963705971466163 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12107719176915404177 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 105, 118, 105, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7745963705971466163 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6915795498251309240 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1969170405 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9682542540652215502 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6321357738359175961 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3442489376193643473 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,17346329855125638572 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [113, 117, 101, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7745963705971466163 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6688036184593315617 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7745963705971466163 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15406842777469414839 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2108750218 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2406607294583069661 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4717867088114969182 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2208468403280602834 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15019582128715852139 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 116, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7745963705971466163 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3858448905473805437 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2150252389389974561 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 117, 112, 101, 114, 112, 111, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4010746123738810474 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 109, 112, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4150572531303135249 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10345343673349999630 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14279258857110558246 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,663695920148620978 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 384311930 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5082039833444622218 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9035313278791088773 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15646143712793708965 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,863155778224174120 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14279258857110558246 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8212555005843622573 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14279258857110558246 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13121609406971009111 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14279258857110558246 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10099215157636821877 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 849718559 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15230479297382651730 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1971879451351582109 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8527147975510211069 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9475598447938262544 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 66, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14279258857110558246 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13865731640900190553 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14279258857110558246 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14058514772924014246 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 97, 98, 105, 110, 111, 119, 105, 116, 115, 99, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14279258857110558246 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4599307321526781213 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_processNewEq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_processNewDiseq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_ring___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_check_x27___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_checkInvariants___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = crate::leanh::lean_unsigned_to_nat(3846929371);
    v___x_644_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_645_ = l_Lean_Name_num___override(v___x_644_, v___x_643_);
    return v___x_645_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_647_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_648_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_);
    v___x_649_ = l_Lean_Name_str___override(v___x_648_, v___x_647_);
    return v___x_649_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_651_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_652_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_);
    v___x_653_ = l_Lean_Name_str___override(v___x_652_, v___x_651_);
    return v___x_653_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_654_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_655_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_);
    v___x_656_ = l_Lean_Name_num___override(v___x_655_, v___x_654_);
    return v___x_656_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_659_ = 0;
    v___x_660_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_);
    v___x_661_ = l_Lean_registerTraceClass(v___x_658_, v___x_659_, v___x_660_);
    return v___x_661_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2____boxed(
    mut v_a_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_663_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_();
    return v_res_663_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_669_ = crate::leanh::lean_unsigned_to_nat(2457222630);
    v___x_670_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_671_ = l_Lean_Name_num___override(v___x_670_, v___x_669_);
    return v___x_671_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_673_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_);
    v___x_674_ = l_Lean_Name_str___override(v___x_673_, v___x_672_);
    return v___x_674_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_676_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_);
    v___x_677_ = l_Lean_Name_str___override(v___x_676_, v___x_675_);
    return v___x_677_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_679_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_);
    v___x_680_ = l_Lean_Name_num___override(v___x_679_, v___x_678_);
    return v___x_680_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: u8 = 0;
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_;
    v___x_683_ = 0;
    v___x_684_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_);
    v___x_685_ = l_Lean_registerTraceClass(v___x_682_, v___x_683_, v___x_684_);
    return v___x_685_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2____boxed(
    mut v_a_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_687_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_();
    return v_res_687_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = crate::leanh::lean_unsigned_to_nat(3098732122);
    v___x_694_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_695_ = l_Lean_Name_num___override(v___x_694_, v___x_693_);
    return v___x_695_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_697_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_);
    v___x_698_ = l_Lean_Name_str___override(v___x_697_, v___x_696_);
    return v___x_698_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_);
    v___x_701_ = l_Lean_Name_str___override(v___x_700_, v___x_699_);
    return v___x_701_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_702_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_703_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_);
    v___x_704_ = l_Lean_Name_num___override(v___x_703_, v___x_702_);
    return v___x_704_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: u8 = 0;
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_;
    v___x_707_ = 0;
    v___x_708_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_);
    v___x_709_ = l_Lean_registerTraceClass(v___x_706_, v___x_707_, v___x_708_);
    return v___x_709_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2____boxed(
    mut v_a_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_711_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_();
    return v_res_711_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_718_ = crate::leanh::lean_unsigned_to_nat(2186548928);
    v___x_719_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_720_ = l_Lean_Name_num___override(v___x_719_, v___x_718_);
    return v___x_720_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_722_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_);
    v___x_723_ = l_Lean_Name_str___override(v___x_722_, v___x_721_);
    return v___x_723_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_725_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_);
    v___x_726_ = l_Lean_Name_str___override(v___x_725_, v___x_724_);
    return v___x_726_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_728_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_);
    v___x_729_ = l_Lean_Name_num___override(v___x_728_, v___x_727_);
    return v___x_729_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: u8 = 0;
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_;
    v___x_732_ = 1;
    v___x_733_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_);
    v___x_734_ = l_Lean_registerTraceClass(v___x_731_, v___x_732_, v___x_733_);
    return v___x_734_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2____boxed(
    mut v_a_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_736_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_();
    return v_res_736_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_;
    v___x_757_ = 1;
    v___x_758_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_;
    v___x_759_ = l_Lean_registerTraceClass(v___x_756_, v___x_757_, v___x_758_);
    return v___x_759_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2____boxed(
    mut v_a_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_761_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_();
    return v_res_761_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = crate::leanh::lean_unsigned_to_nat(3179228936);
    v___x_769_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_770_ = l_Lean_Name_num___override(v___x_769_, v___x_768_);
    return v___x_770_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_772_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_);
    v___x_773_ = l_Lean_Name_str___override(v___x_772_, v___x_771_);
    return v___x_773_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_775_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_);
    v___x_776_ = l_Lean_Name_str___override(v___x_775_, v___x_774_);
    return v___x_776_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_778_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_);
    v___x_779_ = l_Lean_Name_num___override(v___x_778_, v___x_777_);
    return v___x_779_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: u8 = 0;
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_781_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_;
    v___x_782_ = 1;
    v___x_783_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_);
    v___x_784_ = l_Lean_registerTraceClass(v___x_781_, v___x_782_, v___x_783_);
    return v___x_784_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2____boxed(
    mut v_a_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_();
    return v_res_786_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_;
    v___x_807_ = 1;
    v___x_808_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_;
    v___x_809_ = l_Lean_registerTraceClass(v___x_806_, v___x_807_, v___x_808_);
    return v___x_809_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2____boxed(
    mut v_a_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_();
    return v_res_811_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = crate::leanh::lean_unsigned_to_nat(3534157571);
    v___x_819_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_820_ = l_Lean_Name_num___override(v___x_819_, v___x_818_);
    return v___x_820_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_);
    v___x_823_ = l_Lean_Name_str___override(v___x_822_, v___x_821_);
    return v___x_823_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_825_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_);
    v___x_826_ = l_Lean_Name_str___override(v___x_825_, v___x_824_);
    return v___x_826_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_);
    v___x_829_ = l_Lean_Name_num___override(v___x_828_, v___x_827_);
    return v___x_829_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: u8 = 0;
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_;
    v___x_832_ = 1;
    v___x_833_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_);
    v___x_834_ = l_Lean_registerTraceClass(v___x_831_, v___x_832_, v___x_833_);
    return v___x_834_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2____boxed(
    mut v_a_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_();
    return v_res_836_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_842_ = crate::leanh::lean_unsigned_to_nat(3068134925);
    v___x_843_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_844_ = l_Lean_Name_num___override(v___x_843_, v___x_842_);
    return v___x_844_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_845_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_846_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_);
    v___x_847_ = l_Lean_Name_str___override(v___x_846_, v___x_845_);
    return v___x_847_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_849_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_);
    v___x_850_ = l_Lean_Name_str___override(v___x_849_, v___x_848_);
    return v___x_850_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_852_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_);
    v___x_853_ = l_Lean_Name_num___override(v___x_852_, v___x_851_);
    return v___x_853_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: u8 = 0;
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_;
    v___x_856_ = 0;
    v___x_857_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_);
    v___x_858_ = l_Lean_registerTraceClass(v___x_855_, v___x_856_, v___x_857_);
    return v___x_858_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2____boxed(
    mut v_a_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_860_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_();
    return v_res_860_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = crate::leanh::lean_unsigned_to_nat(2227562522);
    v___x_867_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_868_ = l_Lean_Name_num___override(v___x_867_, v___x_866_);
    return v___x_868_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_870_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_);
    v___x_871_ = l_Lean_Name_str___override(v___x_870_, v___x_869_);
    return v___x_871_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_873_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_);
    v___x_874_ = l_Lean_Name_str___override(v___x_873_, v___x_872_);
    return v___x_874_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_);
    v___x_877_ = l_Lean_Name_num___override(v___x_876_, v___x_875_);
    return v___x_877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_;
    v___x_880_ = 0;
    v___x_881_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_);
    v___x_882_ = l_Lean_registerTraceClass(v___x_879_, v___x_880_, v___x_881_);
    return v___x_882_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2____boxed(
    mut v_a_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_884_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_();
    return v_res_884_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = crate::leanh::lean_unsigned_to_nat(3134173114);
    v___x_891_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_892_ = l_Lean_Name_num___override(v___x_891_, v___x_890_);
    return v___x_892_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_893_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_);
    v___x_895_ = l_Lean_Name_str___override(v___x_894_, v___x_893_);
    return v___x_895_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_897_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_);
    v___x_898_ = l_Lean_Name_str___override(v___x_897_, v___x_896_);
    return v___x_898_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_900_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_);
    v___x_901_ = l_Lean_Name_num___override(v___x_900_, v___x_899_);
    return v___x_901_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: u8 = 0;
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_;
    v___x_904_ = 0;
    v___x_905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_);
    v___x_906_ = l_Lean_registerTraceClass(v___x_903_, v___x_904_, v___x_905_);
    return v___x_906_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2____boxed(
    mut v_a_907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_908_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_();
    return v_res_908_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_928_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_;
    v___x_929_ = 0;
    v___x_930_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_;
    v___x_931_ = l_Lean_registerTraceClass(v___x_928_, v___x_929_, v___x_930_);
    return v___x_931_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2____boxed(
    mut v_a_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_933_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_();
    return v_res_933_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = crate::leanh::lean_unsigned_to_nat(4257455002);
    v___x_941_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_942_ = l_Lean_Name_num___override(v___x_941_, v___x_940_);
    return v___x_942_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_944_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_);
    v___x_945_ = l_Lean_Name_str___override(v___x_944_, v___x_943_);
    return v___x_945_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_947_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_);
    v___x_948_ = l_Lean_Name_str___override(v___x_947_, v___x_946_);
    return v___x_948_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_950_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_);
    v___x_951_ = l_Lean_Name_num___override(v___x_950_, v___x_949_);
    return v___x_951_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: u8 = 0;
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_953_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_;
    v___x_954_ = 0;
    v___x_955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_);
    v___x_956_ = l_Lean_registerTraceClass(v___x_953_, v___x_954_, v___x_955_);
    return v___x_956_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2____boxed(
    mut v_a_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_958_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_();
    return v_res_958_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_965_ = crate::leanh::lean_unsigned_to_nat(4255071972);
    v___x_966_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_967_ = l_Lean_Name_num___override(v___x_966_, v___x_965_);
    return v___x_967_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_969_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_);
    v___x_970_ = l_Lean_Name_str___override(v___x_969_, v___x_968_);
    return v___x_970_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_971_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_972_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_);
    v___x_973_ = l_Lean_Name_str___override(v___x_972_, v___x_971_);
    return v___x_973_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_975_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_);
    v___x_976_ = l_Lean_Name_num___override(v___x_975_, v___x_974_);
    return v___x_976_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_;
    v___x_979_ = 0;
    v___x_980_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_);
    v___x_981_ = l_Lean_registerTraceClass(v___x_978_, v___x_979_, v___x_980_);
    return v___x_981_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2____boxed(
    mut v_a_982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_983_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_();
    return v_res_983_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1002_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_;
    v___x_1003_ = 0;
    v___x_1004_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_;
    v___x_1005_ = l_Lean_registerTraceClass(v___x_1002_, v___x_1003_, v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2____boxed(
    mut v_a_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1007_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_();
    return v_res_1007_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = crate::leanh::lean_unsigned_to_nat(3800764929);
    v___x_1015_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1016_ = l_Lean_Name_num___override(v___x_1015_, v___x_1014_);
    return v___x_1016_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1018_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_);
    v___x_1019_ = l_Lean_Name_str___override(v___x_1018_, v___x_1017_);
    return v___x_1019_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1021_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_);
    v___x_1022_ = l_Lean_Name_str___override(v___x_1021_, v___x_1020_);
    return v___x_1022_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1024_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_);
    v___x_1025_ = l_Lean_Name_num___override(v___x_1024_, v___x_1023_);
    return v___x_1025_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1027_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_;
    v___x_1028_ = 0;
    v___x_1029_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_);
    v___x_1030_ = l_Lean_registerTraceClass(v___x_1027_, v___x_1028_, v___x_1029_);
    return v___x_1030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2____boxed(
    mut v_a_1031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1032_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_();
    return v_res_1032_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = crate::leanh::lean_unsigned_to_nat(3383779916);
    v___x_1039_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1040_ = l_Lean_Name_num___override(v___x_1039_, v___x_1038_);
    return v___x_1040_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1041_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1042_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_);
    v___x_1043_ = l_Lean_Name_str___override(v___x_1042_, v___x_1041_);
    return v___x_1043_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1045_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_);
    v___x_1046_ = l_Lean_Name_str___override(v___x_1045_, v___x_1044_);
    return v___x_1046_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1047_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_);
    v___x_1049_ = l_Lean_Name_num___override(v___x_1048_, v___x_1047_);
    return v___x_1049_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: u8 = 0;
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_;
    v___x_1052_ = 0;
    v___x_1053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_);
    v___x_1054_ = l_Lean_registerTraceClass(v___x_1051_, v___x_1052_, v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2____boxed(
    mut v_a_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_();
    return v_res_1056_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1063_ = crate::leanh::lean_unsigned_to_nat(3006444232);
    v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1065_ = l_Lean_Name_num___override(v___x_1064_, v___x_1063_);
    return v___x_1065_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1067_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_);
    v___x_1068_ = l_Lean_Name_str___override(v___x_1067_, v___x_1066_);
    return v___x_1068_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1070_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_);
    v___x_1071_ = l_Lean_Name_str___override(v___x_1070_, v___x_1069_);
    return v___x_1071_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1073_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_);
    v___x_1074_ = l_Lean_Name_num___override(v___x_1073_, v___x_1072_);
    return v___x_1074_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_;
    v___x_1077_ = 0;
    v___x_1078_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_);
    v___x_1079_ = l_Lean_registerTraceClass(v___x_1076_, v___x_1077_, v___x_1078_);
    return v___x_1079_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2____boxed(
    mut v_a_1080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1081_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_();
    return v_res_1081_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_(
    mut v___x_1082_: u8,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
    mut v___y_1086_: *mut crate::leanh::LeanObject,
    mut v___y_1087_: *mut crate::leanh::LeanObject,
    mut v___y_1088_: *mut crate::leanh::LeanObject,
    mut v___y_1089_: *mut crate::leanh::LeanObject,
    mut v___y_1090_: *mut crate::leanh::LeanObject,
    mut v___y_1091_: *mut crate::leanh::LeanObject,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = crate::leanh::lean_box((v___x_1082_) as usize);
    v___x_1095_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2____boxed(
    mut v___x_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
    mut v___y_1098_: *mut crate::leanh::LeanObject,
    mut v___y_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
    mut v___y_1103_: *mut crate::leanh::LeanObject,
    mut v___y_1104_: *mut crate::leanh::LeanObject,
    mut v___y_1105_: *mut crate::leanh::LeanObject,
    mut v___y_1106_: *mut crate::leanh::LeanObject,
    mut v___y_1107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_495__boxed_1108_: u8 = 0;
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_495__boxed_1108_ = (crate::leanh::lean_unbox(v___x_1096_) as u8);
    v_res_1109_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_(v___x_495__boxed_1108_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
    crate::leanh::lean_dec(v___y_1106_);
    crate::leanh::lean_dec_ref(v___y_1105_);
    crate::leanh::lean_dec(v___y_1104_);
    crate::leanh::lean_dec_ref(v___y_1103_);
    crate::leanh::lean_dec(v___y_1102_);
    crate::leanh::lean_dec_ref(v___y_1101_);
    crate::leanh::lean_dec(v___y_1100_);
    crate::leanh::lean_dec_ref(v___y_1099_);
    crate::leanh::lean_dec(v___y_1098_);
    crate::leanh::lean_dec(v___y_1097_);
    return v_res_1109_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_1121_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_;
    v___x_1122_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_;
    v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_;
    v___f_1124_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_;
    v___x_1125_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_;
    v___x_1126_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_;
    v___x_1127_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_;
    v___x_1128_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(
        v___x_1120_,
        v___x_1121_,
        v___x_1122_,
        v___x_1123_,
        v___f_1124_,
        v___x_1125_,
        v___x_1126_,
        v___x_1127_,
    );
    return v___x_1128_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2____boxed(
    mut v_a_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_();
    return v_res_1130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin);
}
