// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Tactic.Grind.Arith.Linear.Util Lean.Meta.Tactic.Grind.Arith.Linear.Var Lean.Meta.Tactic.Grind.Arith.Linear.StructId Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr Lean.Meta.Tactic.Grind.Arith.Linear.Reify Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr Lean.Meta.Tactic.Grind.Arith.Linear.Proof Lean.Meta.Tactic.Grind.Arith.Linear.SearchM Lean.Meta.Tactic.Grind.Arith.Linear.Search Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq Lean.Meta.Tactic.Grind.Arith.Linear.Internalize Lean.Meta.Tactic.Grind.Arith.Linear.Model Lean.Meta.Tactic.Grind.Arith.Linear.PP Lean.Meta.Tactic.Grind.Arith.Linear.Inv Lean.Meta.Tactic.Grind.Arith.Linear.MBTC Lean.Meta.Tactic.Grind.Arith.Linear.VarRename Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule Lean.Meta.Tactic.Grind.Arith.Linear.Action
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Action::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Action,
    l_Lean_Meta_Grind_Action_linarith___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Action,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::IneqCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Internalize::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize,
    l_Lean_Meta_Grind_Arith_Linear_internalize___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Inv::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv,
    l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::MBTC::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC,
    l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Model::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::OfNatModule::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::PP::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Proof::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::PropagateEq::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq,
    l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed,
    l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Reify::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Search::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search,
    l_Lean_Meta_Grind_Arith_Linear_check___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::SearchM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::StructId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::ToExpr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types, l_Lean_Meta_Grind_Arith_Linear_linearExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Var::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::VarRename::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_SolverExtension_setMethods___redArg;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 105, 110, 97, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10740975855909177240 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,622053547050603573 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7655114909728474417 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 101, 97, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12910735170446905988 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,11406156400825489893 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14480710909064726704 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,901512620297137340 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7744276054051878070 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11108415085817239878 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6797098513001089983 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13701912692371634398 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,373506095338336639 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1102154159098576050 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,996731684289135590 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11502001202432388283 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12664108271019058381 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2305540771362987769 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15918301331542977900 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1977064142 as usize) << 1) | 1) as *mut leanh::LeanObject,7417645149003085178 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16556610582215774293 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1529149417620901525 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3306862960215173400 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10740975855909177240 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15515019119152942329 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 864946378 as usize) << 1) | 1) as *mut leanh::LeanObject,13690862708765147858 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3788409093887814173 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10378635673631711869 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,9755278745623324816 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10740975855909177240 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11874191766470140998 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 111, 100, 101, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10740975855909177240 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4796074624638123820 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 273425714 as usize) << 1) | 1) as *mut leanh::LeanObject,2963104455244773325 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7428116533324330926 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9712579851092265346 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,15670247312357657051 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [117, 110, 115, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10740975855909177240 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11874191766470140998 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12251249472348757592 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 118464817 as usize) << 1) | 1) as *mut leanh::LeanObject,17225769077707953609 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2319318154291305306 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1563079709895239718 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,5128966920653484391 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 114, 105, 118, 105, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10740975855909177240 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11874191766470140998 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value) as *mut leanh::LeanObject,434644203296494385 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 116, 111, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10740975855909177240 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11874191766470140998 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13803741813067519852 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1769673126 as usize) << 1) | 1) as *mut leanh::LeanObject,6692721068207693840 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4659643493673970823 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7089449360825956047 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,846502168678007690 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 103, 110, 111, 114, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10740975855909177240 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11874191766470140998 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3157941449954247617 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 101, 97, 114, 99, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6125775157677286871 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12408982493536103924 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1878016030 as usize) << 1) | 1) as *mut leanh::LeanObject,6978563426347047402 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5011607175103671077 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5213205549713280197 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3622370397323823880 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 102, 108, 105, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6125775157677286871 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12408982493536103924 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4410520792035975192 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 356702522 as usize) << 1) | 1) as *mut leanh::LeanObject,1133143035730183124 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6814242713924597915 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5272142115989376123 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,13680961559077737486 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 105, 103, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6125775157677286871 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12408982493536103924 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10502968884285528847 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1398474614 as usize) << 1) | 1) as *mut leanh::LeanObject,701115512598092494 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1387519409650435353 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10419788142102615505 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,15878821056021350316 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6125775157677286871 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12408982493536103924 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10500880470362630306 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1427258088 as usize) << 1) | 1) as *mut leanh::LeanObject,8648436131535879925 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7024810436472568678 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3034979686550151450 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,6220639037790929923 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [98, 97, 99, 107, 116, 114, 97, 99, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6125775157677286871 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12408982493536103924 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4420802780582884802 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 117, 98, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6125775157677286871 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5181136723825328589 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Linear_internalize___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_linarith___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Linear_check___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: u8 = 0;
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_537_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_538_ = 0;
    v___x_539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_540_ = l_Lean_registerTraceClass(v___x_537_, v___x_538_, v___x_539_);
    return v___x_540_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2____boxed(
    mut v_a_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_542_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_();
    return v_res_542_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: u8 = 0;
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_;
    v___x_562_ = 0;
    v___x_563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_;
    v___x_564_ = l_Lean_registerTraceClass(v___x_561_, v___x_562_, v___x_563_);
    return v___x_564_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2____boxed(
    mut v_a_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_566_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_();
    return v_res_566_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = leanh::lean_unsigned_to_nat(2867706376);
    v___x_573_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_574_ = l_Lean_Name_num___override(v___x_573_, v___x_572_);
    return v___x_574_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_575_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_576_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_);
    v___x_577_ = l_Lean_Name_str___override(v___x_576_, v___x_575_);
    return v___x_577_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_579_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_);
    v___x_580_ = l_Lean_Name_str___override(v___x_579_, v___x_578_);
    return v___x_580_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_581_ = leanh::lean_unsigned_to_nat(2);
    v___x_582_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_);
    v___x_583_ = l_Lean_Name_num___override(v___x_582_, v___x_581_);
    return v___x_583_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_585_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_;
    v___x_586_ = 0;
    v___x_587_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_);
    v___x_588_ = l_Lean_registerTraceClass(v___x_585_, v___x_586_, v___x_587_);
    return v___x_588_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2____boxed(
    mut v_a_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_590_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_();
    return v_res_590_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_609_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_;
    v___x_610_ = 0;
    v___x_611_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_;
    v___x_612_ = l_Lean_registerTraceClass(v___x_609_, v___x_610_, v___x_611_);
    return v___x_612_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2____boxed(
    mut v_a_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_614_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_();
    return v_res_614_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_;
    v___x_635_ = 1;
    v___x_636_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_;
    v___x_637_ = l_Lean_registerTraceClass(v___x_634_, v___x_635_, v___x_636_);
    return v___x_637_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2____boxed(
    mut v_a_638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_639_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_();
    return v_res_639_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = leanh::lean_unsigned_to_nat(3761402091);
    v___x_647_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_648_ = l_Lean_Name_num___override(v___x_647_, v___x_646_);
    return v___x_648_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_649_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_650_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_);
    v___x_651_ = l_Lean_Name_str___override(v___x_650_, v___x_649_);
    return v___x_651_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_653_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_);
    v___x_654_ = l_Lean_Name_str___override(v___x_653_, v___x_652_);
    return v___x_654_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_655_ = leanh::lean_unsigned_to_nat(2);
    v___x_656_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_);
    v___x_657_ = l_Lean_Name_num___override(v___x_656_, v___x_655_);
    return v___x_657_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: u8 = 0;
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_;
    v___x_660_ = 1;
    v___x_661_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_);
    v___x_662_ = l_Lean_registerTraceClass(v___x_659_, v___x_660_, v___x_661_);
    return v___x_662_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2____boxed(
    mut v_a_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_664_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_();
    return v_res_664_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_;
    v___x_685_ = 1;
    v___x_686_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_;
    v___x_687_ = l_Lean_registerTraceClass(v___x_684_, v___x_685_, v___x_686_);
    return v___x_687_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2____boxed(
    mut v_a_688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_689_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_();
    return v_res_689_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = leanh::lean_unsigned_to_nat(2188899847);
    v___x_697_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_698_ = l_Lean_Name_num___override(v___x_697_, v___x_696_);
    return v___x_698_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_700_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_);
    v___x_701_ = l_Lean_Name_str___override(v___x_700_, v___x_699_);
    return v___x_701_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_702_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_703_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_);
    v___x_704_ = l_Lean_Name_str___override(v___x_703_, v___x_702_);
    return v___x_704_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_705_ = leanh::lean_unsigned_to_nat(2);
    v___x_706_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_);
    v___x_707_ = l_Lean_Name_num___override(v___x_706_, v___x_705_);
    return v___x_707_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: u8 = 0;
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_;
    v___x_710_ = 1;
    v___x_711_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_);
    v___x_712_ = l_Lean_registerTraceClass(v___x_709_, v___x_710_, v___x_711_);
    return v___x_712_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2____boxed(
    mut v_a_713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_714_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_();
    return v_res_714_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_;
    v___x_736_ = 0;
    v___x_737_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_;
    v___x_738_ = l_Lean_registerTraceClass(v___x_735_, v___x_736_, v___x_737_);
    return v___x_738_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2____boxed(
    mut v_a_739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_740_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_();
    return v_res_740_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: u8 = 0;
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_;
    v___x_762_ = 1;
    v___x_763_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_;
    v___x_764_ = l_Lean_registerTraceClass(v___x_761_, v___x_762_, v___x_763_);
    return v___x_764_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2____boxed(
    mut v_a_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_();
    return v_res_766_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: u8 = 0;
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_;
    v___x_788_ = 1;
    v___x_789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_;
    v___x_790_ = l_Lean_registerTraceClass(v___x_787_, v___x_788_, v___x_789_);
    return v___x_790_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2____boxed(
    mut v_a_791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_792_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_();
    return v_res_792_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: u8 = 0;
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_;
    v___x_814_ = 1;
    v___x_815_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_;
    v___x_816_ = l_Lean_registerTraceClass(v___x_813_, v___x_814_, v___x_815_);
    return v___x_816_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2____boxed(
    mut v_a_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_818_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_();
    return v_res_818_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = leanh::lean_unsigned_to_nat(3602332852);
    v___x_827_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_828_ = l_Lean_Name_num___override(v___x_827_, v___x_826_);
    return v___x_828_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_830_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_);
    v___x_831_ = l_Lean_Name_str___override(v___x_830_, v___x_829_);
    return v___x_831_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_833_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_);
    v___x_834_ = l_Lean_Name_str___override(v___x_833_, v___x_832_);
    return v___x_834_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = leanh::lean_unsigned_to_nat(2);
    v___x_836_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_);
    v___x_837_ = l_Lean_Name_num___override(v___x_836_, v___x_835_);
    return v___x_837_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: u8 = 0;
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_;
    v___x_840_ = 1;
    v___x_841_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_);
    v___x_842_ = l_Lean_registerTraceClass(v___x_839_, v___x_840_, v___x_841_);
    return v___x_842_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2____boxed(
    mut v_a_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_();
    return v_res_844_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = leanh::lean_unsigned_to_nat(2917960733);
    v___x_852_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_853_ = l_Lean_Name_num___override(v___x_852_, v___x_851_);
    return v___x_853_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_855_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_);
    v___x_856_ = l_Lean_Name_str___override(v___x_855_, v___x_854_);
    return v___x_856_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_;
    v___x_858_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_);
    v___x_859_ = l_Lean_Name_str___override(v___x_858_, v___x_857_);
    return v___x_859_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = leanh::lean_unsigned_to_nat(2);
    v___x_861_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_);
    v___x_862_ = l_Lean_Name_num___override(v___x_861_, v___x_860_);
    return v___x_862_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_;
    v___x_865_ = 0;
    v___x_866_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_);
    v___x_867_ = l_Lean_registerTraceClass(v___x_864_, v___x_865_, v___x_866_);
    return v___x_867_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2____boxed(
    mut v_a_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_869_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_();
    return v_res_869_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_878_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_879_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_;
    v___x_880_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_;
    v___x_881_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_;
    v___x_882_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_;
    v___x_883_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_;
    v___x_884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_;
    v___x_885_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_;
    v___x_886_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(
        v___x_878_, v___x_879_, v___x_880_, v___x_881_, v___x_882_, v___x_883_, v___x_884_,
        v___x_885_,
    );
    return v___x_886_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2____boxed(
    mut v_a_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_();
    return v_res_888_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Action(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Action(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear(builtin);
}