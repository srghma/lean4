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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,622053547050603573 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,7655114909728474417 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 109, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14785409762281932364 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,12833161325241227853 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15948583408990530872 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,16046516903769087636 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,12688987844954821806 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,1628631271144195566 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,11403964697897510527 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,6647257981682712606 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,6727373836467124671 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14503154075155024370 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,2181067493093289894 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,1060138090082246139 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15880579792917111949 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,8204911064715934137 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,5774094994212982820 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value) as *mut LeanObject,13114681713692780684 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut LeanObject,7745963705971466163 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [117, 110, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut LeanObject,7745963705971466163 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value) as *mut LeanObject,12107719176915404177 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 105, 118, 105, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut LeanObject,7745963705971466163 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject,6915795498251309240 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,((( 1969170405 as usize) << 1) | 1) as *mut LeanObject,9682542540652215502 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,6321357738359175961 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,3442489376193643473 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,17346329855125638572 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [113, 117, 101, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut LeanObject,7745963705971466163 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value) as *mut LeanObject,6688036184593315617 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut LeanObject,7745963705971466163 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject,15406842777469414839 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,((( 2108750218 as usize) << 1) | 1) as *mut LeanObject,2406607294583069661 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4717867088114969182 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,2208468403280602834 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,15019582128715852139 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 116, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__value) as *mut LeanObject,7745963705971466163 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value) as *mut LeanObject,3858448905473805437 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value) as *mut LeanObject,2150252389389974561 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 117, 112, 101, 114, 112, 111, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value) as *mut LeanObject,4010746123738810474 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 109, 112, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,4150572531303135249 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value) as *mut LeanObject,10345343673349999630 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14279258857110558246 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__value) as *mut LeanObject,663695920148620978 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,((( 384311930 as usize) << 1) | 1) as *mut LeanObject,5082039833444622218 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,9035313278791088773 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15646143712793708965 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,863155778224174120 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14279258857110558246 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value) as *mut LeanObject,8212555005843622573 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14279258857110558246 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value) as *mut LeanObject,13121609406971009111 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14279258857110558246 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__value) as *mut LeanObject,10099215157636821877 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,((( 849718559 as usize) << 1) | 1) as *mut LeanObject,15230479297382651730 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,1971879451351582109 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,8527147975510211069 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,9475598447938262544 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 66, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14279258857110558246 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value) as *mut LeanObject,13865731640900190553 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14279258857110558246 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2__value) as *mut LeanObject,14058514772924014246 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [114, 97, 98, 105, 110, 111, 119, 105, 116, 115, 99, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__value) as *mut LeanObject,14279258857110558246 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value) as *mut LeanObject,4599307321526781213 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_processNewEq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_processNewDiseq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_ring___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_check_x27___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_CommRing_checkInvariants___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    v___x_643_ = lean_unsigned_to_nat(3846929371);
    v___x_644_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_645_ = l_Lean_Name_num___override(v___x_644_, v___x_643_);
    return v___x_645_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    v___x_647_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_648_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_);
    v___x_649_ = l_Lean_Name_str___override(v___x_648_, v___x_647_);
    return v___x_649_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    v___x_651_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_652_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_);
    v___x_653_ = l_Lean_Name_str___override(v___x_652_, v___x_651_);
    return v___x_653_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    v___x_654_ = lean_unsigned_to_nat(2);
    v___x_655_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_);
    v___x_656_ = l_Lean_Name_num___override(v___x_655_, v___x_654_);
    return v___x_656_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_659_ = 0;
    v___x_660_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_);
    v___x_661_ = l_Lean_registerTraceClass(v___x_658_, v___x_659_, v___x_660_);
    return v___x_661_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2____boxed(
    mut v_a_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_663_: *mut LeanObject = core::ptr::null_mut();
    v_res_663_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_();
    return v_res_663_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    v___x_669_ = lean_unsigned_to_nat(2457222630);
    v___x_670_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_671_ = l_Lean_Name_num___override(v___x_670_, v___x_669_);
    return v___x_671_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    v___x_672_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_673_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_);
    v___x_674_ = l_Lean_Name_str___override(v___x_673_, v___x_672_);
    return v___x_674_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    v___x_675_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_676_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_);
    v___x_677_ = l_Lean_Name_str___override(v___x_676_, v___x_675_);
    return v___x_677_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v___x_678_ = lean_unsigned_to_nat(2);
    v___x_679_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_);
    v___x_680_ = l_Lean_Name_num___override(v___x_679_, v___x_678_);
    return v___x_680_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: u8 = 0;
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    v___x_682_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_;
    v___x_683_ = 0;
    v___x_684_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_);
    v___x_685_ = l_Lean_registerTraceClass(v___x_682_, v___x_683_, v___x_684_);
    return v___x_685_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2____boxed(
    mut v_a_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_687_: *mut LeanObject = core::ptr::null_mut();
    v_res_687_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_();
    return v_res_687_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    v___x_693_ = lean_unsigned_to_nat(3098732122);
    v___x_694_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_695_ = l_Lean_Name_num___override(v___x_694_, v___x_693_);
    return v___x_695_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v___x_696_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_697_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_);
    v___x_698_ = l_Lean_Name_str___override(v___x_697_, v___x_696_);
    return v___x_698_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    v___x_699_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_700_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_);
    v___x_701_ = l_Lean_Name_str___override(v___x_700_, v___x_699_);
    return v___x_701_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    v___x_702_ = lean_unsigned_to_nat(2);
    v___x_703_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_);
    v___x_704_ = l_Lean_Name_num___override(v___x_703_, v___x_702_);
    return v___x_704_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: u8 = 0;
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    v___x_706_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_;
    v___x_707_ = 0;
    v___x_708_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_);
    v___x_709_ = l_Lean_registerTraceClass(v___x_706_, v___x_707_, v___x_708_);
    return v___x_709_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2____boxed(
    mut v_a_710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_711_: *mut LeanObject = core::ptr::null_mut();
    v_res_711_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_();
    return v_res_711_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    v___x_718_ = lean_unsigned_to_nat(2186548928);
    v___x_719_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_720_ = l_Lean_Name_num___override(v___x_719_, v___x_718_);
    return v___x_720_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_722_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_);
    v___x_723_ = l_Lean_Name_str___override(v___x_722_, v___x_721_);
    return v___x_723_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    v___x_724_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_725_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_);
    v___x_726_ = l_Lean_Name_str___override(v___x_725_, v___x_724_);
    return v___x_726_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    v___x_727_ = lean_unsigned_to_nat(2);
    v___x_728_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_);
    v___x_729_ = l_Lean_Name_num___override(v___x_728_, v___x_727_);
    return v___x_729_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: u8 = 0;
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    v___x_731_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_;
    v___x_732_ = 1;
    v___x_733_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_);
    v___x_734_ = l_Lean_registerTraceClass(v___x_731_, v___x_732_, v___x_733_);
    return v___x_734_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2____boxed(
    mut v_a_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_736_: *mut LeanObject = core::ptr::null_mut();
    v_res_736_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_();
    return v_res_736_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    v___x_756_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_;
    v___x_757_ = 1;
    v___x_758_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_;
    v___x_759_ = l_Lean_registerTraceClass(v___x_756_, v___x_757_, v___x_758_);
    return v___x_759_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2____boxed(
    mut v_a_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_761_: *mut LeanObject = core::ptr::null_mut();
    v_res_761_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_();
    return v_res_761_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    v___x_768_ = lean_unsigned_to_nat(3179228936);
    v___x_769_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_770_ = l_Lean_Name_num___override(v___x_769_, v___x_768_);
    return v___x_770_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_772_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_);
    v___x_773_ = l_Lean_Name_str___override(v___x_772_, v___x_771_);
    return v___x_773_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_775_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_);
    v___x_776_ = l_Lean_Name_str___override(v___x_775_, v___x_774_);
    return v___x_776_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    v___x_777_ = lean_unsigned_to_nat(2);
    v___x_778_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_);
    v___x_779_ = l_Lean_Name_num___override(v___x_778_, v___x_777_);
    return v___x_779_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: u8 = 0;
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    v___x_781_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_;
    v___x_782_ = 1;
    v___x_783_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_);
    v___x_784_ = l_Lean_registerTraceClass(v___x_781_, v___x_782_, v___x_783_);
    return v___x_784_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2____boxed(
    mut v_a_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_786_: *mut LeanObject = core::ptr::null_mut();
    v_res_786_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_();
    return v_res_786_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    v___x_806_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_;
    v___x_807_ = 1;
    v___x_808_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_;
    v___x_809_ = l_Lean_registerTraceClass(v___x_806_, v___x_807_, v___x_808_);
    return v___x_809_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2____boxed(
    mut v_a_810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_811_: *mut LeanObject = core::ptr::null_mut();
    v_res_811_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_();
    return v_res_811_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    v___x_818_ = lean_unsigned_to_nat(3534157571);
    v___x_819_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_820_ = l_Lean_Name_num___override(v___x_819_, v___x_818_);
    return v___x_820_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    v___x_821_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_822_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_);
    v___x_823_ = l_Lean_Name_str___override(v___x_822_, v___x_821_);
    return v___x_823_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_825_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_);
    v___x_826_ = l_Lean_Name_str___override(v___x_825_, v___x_824_);
    return v___x_826_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    v___x_827_ = lean_unsigned_to_nat(2);
    v___x_828_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_);
    v___x_829_ = l_Lean_Name_num___override(v___x_828_, v___x_827_);
    return v___x_829_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: u8 = 0;
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    v___x_831_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_;
    v___x_832_ = 1;
    v___x_833_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_);
    v___x_834_ = l_Lean_registerTraceClass(v___x_831_, v___x_832_, v___x_833_);
    return v___x_834_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2____boxed(
    mut v_a_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_836_: *mut LeanObject = core::ptr::null_mut();
    v_res_836_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_();
    return v_res_836_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    v___x_842_ = lean_unsigned_to_nat(3068134925);
    v___x_843_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_844_ = l_Lean_Name_num___override(v___x_843_, v___x_842_);
    return v___x_844_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    v___x_845_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_846_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_);
    v___x_847_ = l_Lean_Name_str___override(v___x_846_, v___x_845_);
    return v___x_847_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_849_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_);
    v___x_850_ = l_Lean_Name_str___override(v___x_849_, v___x_848_);
    return v___x_850_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    v___x_851_ = lean_unsigned_to_nat(2);
    v___x_852_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_);
    v___x_853_ = l_Lean_Name_num___override(v___x_852_, v___x_851_);
    return v___x_853_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: u8 = 0;
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    v___x_855_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_;
    v___x_856_ = 0;
    v___x_857_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_);
    v___x_858_ = l_Lean_registerTraceClass(v___x_855_, v___x_856_, v___x_857_);
    return v___x_858_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2____boxed(
    mut v_a_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_860_: *mut LeanObject = core::ptr::null_mut();
    v_res_860_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_();
    return v_res_860_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    v___x_866_ = lean_unsigned_to_nat(2227562522);
    v___x_867_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_868_ = l_Lean_Name_num___override(v___x_867_, v___x_866_);
    return v___x_868_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    v___x_869_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_870_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_);
    v___x_871_ = l_Lean_Name_str___override(v___x_870_, v___x_869_);
    return v___x_871_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    v___x_872_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_873_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_);
    v___x_874_ = l_Lean_Name_str___override(v___x_873_, v___x_872_);
    return v___x_874_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    v___x_875_ = lean_unsigned_to_nat(2);
    v___x_876_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_);
    v___x_877_ = l_Lean_Name_num___override(v___x_876_, v___x_875_);
    return v___x_877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    v___x_879_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_;
    v___x_880_ = 0;
    v___x_881_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_);
    v___x_882_ = l_Lean_registerTraceClass(v___x_879_, v___x_880_, v___x_881_);
    return v___x_882_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2____boxed(
    mut v_a_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_884_: *mut LeanObject = core::ptr::null_mut();
    v_res_884_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_();
    return v_res_884_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    v___x_890_ = lean_unsigned_to_nat(3134173114);
    v___x_891_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_892_ = l_Lean_Name_num___override(v___x_891_, v___x_890_);
    return v___x_892_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    v___x_893_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_894_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_);
    v___x_895_ = l_Lean_Name_str___override(v___x_894_, v___x_893_);
    return v___x_895_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    v___x_896_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_897_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_);
    v___x_898_ = l_Lean_Name_str___override(v___x_897_, v___x_896_);
    return v___x_898_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    v___x_899_ = lean_unsigned_to_nat(2);
    v___x_900_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_);
    v___x_901_ = l_Lean_Name_num___override(v___x_900_, v___x_899_);
    return v___x_901_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: u8 = 0;
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    v___x_903_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_;
    v___x_904_ = 0;
    v___x_905_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_);
    v___x_906_ = l_Lean_registerTraceClass(v___x_903_, v___x_904_, v___x_905_);
    return v___x_906_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2____boxed(
    mut v_a_907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_908_: *mut LeanObject = core::ptr::null_mut();
    v_res_908_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_();
    return v_res_908_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    v___x_928_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_;
    v___x_929_ = 0;
    v___x_930_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_;
    v___x_931_ = l_Lean_registerTraceClass(v___x_928_, v___x_929_, v___x_930_);
    return v___x_931_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2____boxed(
    mut v_a_932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_933_: *mut LeanObject = core::ptr::null_mut();
    v_res_933_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_();
    return v_res_933_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    v___x_940_ = lean_unsigned_to_nat(4257455002);
    v___x_941_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_942_ = l_Lean_Name_num___override(v___x_941_, v___x_940_);
    return v___x_942_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_944_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_);
    v___x_945_ = l_Lean_Name_str___override(v___x_944_, v___x_943_);
    return v___x_945_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    v___x_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_947_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_);
    v___x_948_ = l_Lean_Name_str___override(v___x_947_, v___x_946_);
    return v___x_948_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    v___x_949_ = lean_unsigned_to_nat(2);
    v___x_950_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_);
    v___x_951_ = l_Lean_Name_num___override(v___x_950_, v___x_949_);
    return v___x_951_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: u8 = 0;
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    v___x_953_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_;
    v___x_954_ = 0;
    v___x_955_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_);
    v___x_956_ = l_Lean_registerTraceClass(v___x_953_, v___x_954_, v___x_955_);
    return v___x_956_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2____boxed(
    mut v_a_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_958_: *mut LeanObject = core::ptr::null_mut();
    v_res_958_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_();
    return v_res_958_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_965_ = lean_unsigned_to_nat(4255071972);
    v___x_966_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_967_ = l_Lean_Name_num___override(v___x_966_, v___x_965_);
    return v___x_967_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    v___x_968_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_969_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_);
    v___x_970_ = l_Lean_Name_str___override(v___x_969_, v___x_968_);
    return v___x_970_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    v___x_971_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_972_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_);
    v___x_973_ = l_Lean_Name_str___override(v___x_972_, v___x_971_);
    return v___x_973_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    v___x_974_ = lean_unsigned_to_nat(2);
    v___x_975_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_);
    v___x_976_ = l_Lean_Name_num___override(v___x_975_, v___x_974_);
    return v___x_976_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_978_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_;
    v___x_979_ = 0;
    v___x_980_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_);
    v___x_981_ = l_Lean_registerTraceClass(v___x_978_, v___x_979_, v___x_980_);
    return v___x_981_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2____boxed(
    mut v_a_982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_983_: *mut LeanObject = core::ptr::null_mut();
    v_res_983_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_();
    return v_res_983_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_1002_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_;
    v___x_1003_ = 0;
    v___x_1004_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_;
    v___x_1005_ = l_Lean_registerTraceClass(v___x_1002_, v___x_1003_, v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2____boxed(
    mut v_a_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1007_: *mut LeanObject = core::ptr::null_mut();
    v_res_1007_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_();
    return v_res_1007_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    v___x_1014_ = lean_unsigned_to_nat(3800764929);
    v___x_1015_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1016_ = l_Lean_Name_num___override(v___x_1015_, v___x_1014_);
    return v___x_1016_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    v___x_1017_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1018_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_);
    v___x_1019_ = l_Lean_Name_str___override(v___x_1018_, v___x_1017_);
    return v___x_1019_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1021_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_);
    v___x_1022_ = l_Lean_Name_str___override(v___x_1021_, v___x_1020_);
    return v___x_1022_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    v___x_1023_ = lean_unsigned_to_nat(2);
    v___x_1024_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_);
    v___x_1025_ = l_Lean_Name_num___override(v___x_1024_, v___x_1023_);
    return v___x_1025_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    v___x_1027_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_;
    v___x_1028_ = 0;
    v___x_1029_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_);
    v___x_1030_ = l_Lean_registerTraceClass(v___x_1027_, v___x_1028_, v___x_1029_);
    return v___x_1030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2____boxed(
    mut v_a_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1032_: *mut LeanObject = core::ptr::null_mut();
    v_res_1032_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_();
    return v_res_1032_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    v___x_1038_ = lean_unsigned_to_nat(3383779916);
    v___x_1039_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1040_ = l_Lean_Name_num___override(v___x_1039_, v___x_1038_);
    return v___x_1040_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1041_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1042_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_);
    v___x_1043_ = l_Lean_Name_str___override(v___x_1042_, v___x_1041_);
    return v___x_1043_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    v___x_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1045_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_);
    v___x_1046_ = l_Lean_Name_str___override(v___x_1045_, v___x_1044_);
    return v___x_1046_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    v___x_1047_ = lean_unsigned_to_nat(2);
    v___x_1048_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_);
    v___x_1049_ = l_Lean_Name_num___override(v___x_1048_, v___x_1047_);
    return v___x_1049_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: u8 = 0;
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    v___x_1051_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_;
    v___x_1052_ = 0;
    v___x_1053_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_);
    v___x_1054_ = l_Lean_registerTraceClass(v___x_1051_, v___x_1052_, v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2____boxed(
    mut v_a_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1056_: *mut LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_();
    return v_res_1056_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    v___x_1063_ = lean_unsigned_to_nat(3006444232);
    v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1065_ = l_Lean_Name_num___override(v___x_1064_, v___x_1063_);
    return v___x_1065_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    v___x_1066_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1067_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_);
    v___x_1068_ = l_Lean_Name_str___override(v___x_1067_, v___x_1066_);
    return v___x_1068_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_;
    v___x_1070_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_);
    v___x_1071_ = l_Lean_Name_str___override(v___x_1070_, v___x_1069_);
    return v___x_1071_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = lean_unsigned_to_nat(2);
    v___x_1073_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_);
    v___x_1074_ = l_Lean_Name_num___override(v___x_1073_, v___x_1072_);
    return v___x_1074_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: u8 = 0;
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    v___x_1076_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_;
    v___x_1077_ = 0;
    v___x_1078_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_);
    v___x_1079_ = l_Lean_registerTraceClass(v___x_1076_, v___x_1077_, v___x_1078_);
    return v___x_1079_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2____boxed(
    mut v_a_1080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1081_: *mut LeanObject = core::ptr::null_mut();
    v_res_1081_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_();
    return v_res_1081_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_(
    mut v___x_1082_: u8,
    mut v___y_1083_: *mut LeanObject,
    mut v___y_1084_: *mut LeanObject,
    mut v___y_1085_: *mut LeanObject,
    mut v___y_1086_: *mut LeanObject,
    mut v___y_1087_: *mut LeanObject,
    mut v___y_1088_: *mut LeanObject,
    mut v___y_1089_: *mut LeanObject,
    mut v___y_1090_: *mut LeanObject,
    mut v___y_1091_: *mut LeanObject,
    mut v___y_1092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    v___x_1094_ = lean_box((v___x_1082_) as usize);
    v___x_1095_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2____boxed(
    mut v___x_1096_: *mut LeanObject,
    mut v___y_1097_: *mut LeanObject,
    mut v___y_1098_: *mut LeanObject,
    mut v___y_1099_: *mut LeanObject,
    mut v___y_1100_: *mut LeanObject,
    mut v___y_1101_: *mut LeanObject,
    mut v___y_1102_: *mut LeanObject,
    mut v___y_1103_: *mut LeanObject,
    mut v___y_1104_: *mut LeanObject,
    mut v___y_1105_: *mut LeanObject,
    mut v___y_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_495__boxed_1108_: u8 = 0;
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v___x_495__boxed_1108_ = (lean_unbox(v___x_1096_) as u8);
    v_res_1109_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_(v___x_495__boxed_1108_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
    lean_dec(v___y_1106_);
    lean_dec_ref(v___y_1105_);
    lean_dec(v___y_1104_);
    lean_dec_ref(v___y_1103_);
    lean_dec(v___y_1102_);
    lean_dec_ref(v___y_1101_);
    lean_dec(v___y_1100_);
    lean_dec_ref(v___y_1099_);
    lean_dec(v___y_1098_);
    lean_dec(v___y_1097_);
    return v_res_1109_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1130_: *mut LeanObject = core::ptr::null_mut();
    v_res_1130_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_();
    return v_res_1130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3846929371____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2457222630____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3098732122____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2186548928____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_1969170405____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3179228936____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2108750218____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3534157571____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3068134925____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2227562522____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3134173114____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_384311930____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4257455002____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_4255071972____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_849718559____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3800764929____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3383779916____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_3006444232____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_2586229517____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Action(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(builtin);
}
