// Lean compiler output
// Module: Lean.Meta.Tactic.Grind
// Imports: Lean.Meta.Tactic.Grind.Attr Lean.Meta.Tactic.Grind.RevertAll Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.MarkNestedSubsingletons Lean.Meta.Tactic.Grind.Inv Lean.Meta.Tactic.Grind.Proof Lean.Meta.Tactic.Grind.Propagate Lean.Meta.Tactic.Grind.PP Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Ctor Lean.Meta.Tactic.Grind.Parser Lean.Meta.Tactic.Grind.EMatchTheorem Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.Main Lean.Meta.Tactic.Grind.CasesMatch Lean.Meta.Tactic.Grind.Arith Lean.Meta.Tactic.Grind.Ext Lean.Meta.Tactic.Grind.MatchCond Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.Diseq Lean.Meta.Tactic.Grind.MBTC Lean.Meta.Tactic.Grind.Lookahead Lean.Meta.Tactic.Grind.LawfulEqCmp Lean.Meta.Tactic.Grind.ReflCmp Lean.Meta.Tactic.Grind.SynthInstance Lean.Meta.Tactic.Grind.AC Lean.Meta.Tactic.Grind.VarRename Lean.Meta.Tactic.Grind.ProofUtil Lean.Meta.Tactic.Grind.PropagateInj Lean.Meta.Tactic.Grind.Order Lean.Meta.Tactic.Grind.Anchor Lean.Meta.Tactic.Grind.Action Lean.Meta.Tactic.Grind.EMatchTheoremParam Lean.Meta.Tactic.Grind.EMatchAction Lean.Meta.Tactic.Grind.Filter Lean.Meta.Tactic.Grind.CollectParams Lean.Meta.Tactic.Grind.Finish Lean.Meta.Tactic.Grind.RegisterCommand
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::{
    initialize_Lean_Meta_Tactic_Grind_AC, runtime_initialize_Lean_Meta_Tactic_Grind_AC,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Action::{
    initialize_Lean_Meta_Tactic_Grind_Action, runtime_initialize_Lean_Meta_Tactic_Grind_Action,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Anchor::{
    initialize_Lean_Meta_Tactic_Grind_Anchor, runtime_initialize_Lean_Meta_Tactic_Grind_Anchor,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::{
    initialize_Lean_Meta_Tactic_Grind_Arith, runtime_initialize_Lean_Meta_Tactic_Grind_Arith,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Attr::{
    initialize_Lean_Meta_Tactic_Grind_Attr, runtime_initialize_Lean_Meta_Tactic_Grind_Attr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Cases::{
    initialize_Lean_Meta_Tactic_Grind_Cases, runtime_initialize_Lean_Meta_Tactic_Grind_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::CasesMatch::{
    initialize_Lean_Meta_Tactic_Grind_CasesMatch,
    runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::CollectParams::{
    initialize_Lean_Meta_Tactic_Grind_CollectParams,
    runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Core::{
    initialize_Lean_Meta_Tactic_Grind_Core, runtime_initialize_Lean_Meta_Tactic_Grind_Core,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Ctor::{
    initialize_Lean_Meta_Tactic_Grind_Ctor, runtime_initialize_Lean_Meta_Tactic_Grind_Ctor,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Diseq::{
    initialize_Lean_Meta_Tactic_Grind_Diseq, runtime_initialize_Lean_Meta_Tactic_Grind_Diseq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatch::{
    initialize_Lean_Meta_Tactic_Grind_EMatch, runtime_initialize_Lean_Meta_Tactic_Grind_EMatch,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchAction::{
    initialize_Lean_Meta_Tactic_Grind_EMatchAction,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheorem::{
    initialize_Lean_Meta_Tactic_Grind_EMatchTheorem,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheoremParam::{
    initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Ext::{
    initialize_Lean_Meta_Tactic_Grind_Ext, runtime_initialize_Lean_Meta_Tactic_Grind_Ext,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Filter::{
    initialize_Lean_Meta_Tactic_Grind_Filter, runtime_initialize_Lean_Meta_Tactic_Grind_Filter,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Finish::{
    initialize_Lean_Meta_Tactic_Grind_Finish, runtime_initialize_Lean_Meta_Tactic_Grind_Finish,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Injection::{
    initialize_Lean_Meta_Tactic_Grind_Injection,
    runtime_initialize_Lean_Meta_Tactic_Grind_Injection,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Inv::{
    initialize_Lean_Meta_Tactic_Grind_Inv, runtime_initialize_Lean_Meta_Tactic_Grind_Inv,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::LawfulEqCmp::{
    initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp,
    runtime_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Lookahead::{
    initialize_Lean_Meta_Tactic_Grind_Lookahead,
    runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MBTC::{
    initialize_Lean_Meta_Tactic_Grind_MBTC, runtime_initialize_Lean_Meta_Tactic_Grind_MBTC,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    initialize_Lean_Meta_Tactic_Grind_Main, runtime_initialize_Lean_Meta_Tactic_Grind_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MarkNestedSubsingletons::{
    initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons,
    runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MatchCond::{
    initialize_Lean_Meta_Tactic_Grind_MatchCond,
    runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MatchDiscrOnly::{
    initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly,
    runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Order::{
    initialize_Lean_Meta_Tactic_Grind_Order, runtime_initialize_Lean_Meta_Tactic_Grind_Order,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::PP::{
    initialize_Lean_Meta_Tactic_Grind_PP, runtime_initialize_Lean_Meta_Tactic_Grind_PP,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Parser::{
    initialize_Lean_Meta_Tactic_Grind_Parser, runtime_initialize_Lean_Meta_Tactic_Grind_Parser,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Proof::{
    initialize_Lean_Meta_Tactic_Grind_Proof, runtime_initialize_Lean_Meta_Tactic_Grind_Proof,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::ProofUtil::{
    initialize_Lean_Meta_Tactic_Grind_ProofUtil,
    runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Propagate::{
    initialize_Lean_Meta_Tactic_Grind_Propagate,
    runtime_initialize_Lean_Meta_Tactic_Grind_Propagate,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagateInj::{
    initialize_Lean_Meta_Tactic_Grind_PropagateInj,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::ReflCmp::{
    initialize_Lean_Meta_Tactic_Grind_ReflCmp, runtime_initialize_Lean_Meta_Tactic_Grind_ReflCmp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::RegisterCommand::{
    initialize_Lean_Meta_Tactic_Grind_RegisterCommand,
    runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::RevertAll::{
    initialize_Lean_Meta_Tactic_Grind_RevertAll,
    runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::VarRename::{
    initialize_Lean_Meta_Tactic_Grind_VarRename,
    runtime_initialize_Lean_Meta_Tactic_Grind_VarRename,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,622053547050603573 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,4012226919819001376 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4309367254995890649 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15280944596163565952 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10671720502158151777 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,736275567197841284 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16623237835278489944 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,612327682104561413 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12613007054577931379 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1240498661 as usize) << 1) | 1) as *mut leanh::LeanObject,3979257302209856059 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5625041798278194816 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17802727010046845540 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3020198571660395901 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4326589831397681760 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1103938016 as usize) << 1) | 1) as *mut leanh::LeanObject,11328300872206798226 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9618061503583471581 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10951728013576683197 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,17360279751568021968 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9465518857834378653 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 964293774 as usize) << 1) | 1) as *mut leanh::LeanObject,12515679881075450983 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7470173896352042508 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4661798815382898232 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,8831643920948479801 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 113, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15878633502362889009 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1498262528 as usize) << 1) | 1) as *mut leanh::LeanObject,5649111733461218769 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5160393085951372978 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2870199158339532510 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3517233162793207407 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4678287893330609914 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [101, 109, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7179266249896474037 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7179266249896474037 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3595227215421608509 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7179266249896474037 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14368885553064227866 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 198996121 as usize) << 1) | 1) as *mut leanh::LeanObject,13902656875069381168 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15967193618145892327 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12332910248931483951 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,7251511402435389482 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7179266249896474037 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14368885553064227866 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18140240192541098437 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 642649038 as usize) << 1) | 1) as *mut leanh::LeanObject,16725582886417677658 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16925771126771063541 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3680719573949849013 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,18079283529570431352 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 108, 97, 121, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7179266249896474037 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14368885553064227866 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6524983955323653406 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 113, 82, 101, 115, 111, 108, 117, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14950941446142498629 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 89146720 as usize) << 1) | 1) as *mut leanh::LeanObject,7271280147815591636 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2313311263721768859 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7499735555845692795 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3779725331563444494 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16551112126483115663 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 789062521 as usize) << 1) | 1) as *mut leanh::LeanObject,14190033874840122758 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9464403675987304321 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2714790421598441209 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,10941566735766205796 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16823078463290117 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 671723160 as usize) << 1) | 1) as *mut leanh::LeanObject,7808705633617722987 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10295004451253541136 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14047892191766168468 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,7241797169410468781 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 97, 110, 100, 105, 100, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16823078463290117 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8684915628547132386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 487703842 as usize) << 1) | 1) as *mut leanh::LeanObject,17985900382487477725 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8298466977782374494 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12405062079021044946 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,6621333286189641579 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 115, 111, 108, 118, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16823078463290117 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15973447275042534777 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [98, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2132164218978770700 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 98, 116, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3746410129963432689 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12545347794981986237 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12545347794981986237 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18234334788844493322 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1723019193 as usize) << 1) | 1) as *mut leanh::LeanObject,16820754503904610308 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7798246937296266283 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8300481181674383851 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,15260730212520027710 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 111, 111, 107, 97, 104, 101, 97, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13680939433876848140 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13680939433876848140 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14080757959702915425 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 114, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13680939433876848140 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8315095477535384964 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1356401647 as usize) << 1) | 1) as *mut leanh::LeanObject,4247990900885994565 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4577259729208998870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17617592093249871786 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,6550792437722798227 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13680939433876848140 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4137541495311671234 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 435833240 as usize) << 1) | 1) as *mut leanh::LeanObject,3216576027743666557 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5341367744467928126 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8169923391068217522 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,13824672166635082635 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 111, 109, 112, 97, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7179266249896474037 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3693069250233053466 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9151073898064737710 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 114, 111, 111, 102, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1833026388428387609 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1216796725022459179 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 114, 111, 111, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3276211962949419647 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1713749687 as usize) << 1) | 1) as *mut leanh::LeanObject,11550398465823178043 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10281176911930317184 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15294160297304827748 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,12563597209922449021 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11850799392639992908 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1374249216 as usize) << 1) | 1) as *mut leanh::LeanObject,8706600500888297519 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11726339362342842404 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8044194804351579696 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3119624569872335841 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 97, 114, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7001264470613250309 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 105, 110, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15754480344910191077 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [102, 111, 114, 97, 108, 108, 80, 114, 111, 112, 97, 103, 97, 116, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9465863317062095934 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14525387916564814106 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 328880924 as usize) << 1) | 1) as *mut leanh::LeanObject,16750737196964452271 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,932200197351713956 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6676144379241508016 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,12283303630753315937 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 110, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10358592954510782631 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1932954739 as usize) << 1) | 1) as *mut leanh::LeanObject,16101260805784417288 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9993966458636317999 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7999573669295914647 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,389420359977823298 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 104, 101, 111, 114, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 99, 116, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13941955079274945004 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16557695801856656380 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 904368556 as usize) << 1) | 1) as *mut leanh::LeanObject,10249431840870015664 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7596296562654692711 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4058920149531040943 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3695362072690395562 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11575801964243397578 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8099443913045902510 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15792589836992725067 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10240559104755110885 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 116, 99, 104, 67, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3290229967450319541 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1279589469 as usize) << 1) | 1) as *mut leanh::LeanObject,5814728356520329718 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12448618681883417809 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8407663147026185065 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,13764683378812650132 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 97, 109, 98, 100, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3290229967450319541 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7399510755181249375 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 901832444 as usize) << 1) | 1) as *mut leanh::LeanObject,18248731422774399822 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16121872985232526489 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15649123485133397329 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,5085331003081024812 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [112, 114, 111, 118, 101, 70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3290229967450319541 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9871136077191002602 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15448887498159686406 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11575801964243397578 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 942114620 as usize) << 1) | 1) as *mut leanh::LeanObject,4279071663933734595 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1336664268342005208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17906755544868239740 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,14687818412639647013 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 111, 118, 101, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6936347780346814288 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 117, 115, 104, 78, 101, 119, 70, 97, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7666958742445354398 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 112, 112, 77, 97, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14521233681675652486 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6116631682018227666 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 152317745 as usize) << 1) | 1) as *mut leanh::LeanObject,9142271493739108744 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5282552047711423407 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9235329369416750871 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,6250597789020794562 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1890696840863774259 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 111, 99, 97, 108, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3989487038582066444 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: u8 = 0;
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1275_ = 0;
    v___x_1276_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1277_ = l_Lean_registerTraceClass(v___x_1274_, v___x_1275_, v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2____boxed(
    mut v_a_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1279_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_();
    return v_res_1279_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: u8 = 0;
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_;
    v___x_1298_ = 0;
    v___x_1299_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_;
    v___x_1300_ = l_Lean_registerTraceClass(v___x_1297_, v___x_1298_, v___x_1299_);
    return v___x_1300_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2____boxed(
    mut v_a_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_();
    return v_res_1302_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_;
    v___x_1321_ = 0;
    v___x_1322_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_;
    v___x_1323_ = l_Lean_registerTraceClass(v___x_1320_, v___x_1321_, v___x_1322_);
    return v___x_1323_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2____boxed(
    mut v_a_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1325_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_();
    return v_res_1325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: u8 = 0;
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_;
    v___x_1344_ = 0;
    v___x_1345_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_;
    v___x_1346_ = l_Lean_registerTraceClass(v___x_1343_, v___x_1344_, v___x_1345_);
    return v___x_1346_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2____boxed(
    mut v_a_1347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1348_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_();
    return v_res_1348_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = leanh::lean_unsigned_to_nat(3999206488);
    v___x_1354_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1355_ = l_Lean_Name_num___override(v___x_1354_, v___x_1353_);
    return v___x_1355_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1357_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
    v___x_1358_ = l_Lean_Name_str___override(v___x_1357_, v___x_1356_);
    return v___x_1358_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1359_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1360_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
    v___x_1361_ = l_Lean_Name_str___override(v___x_1360_, v___x_1359_);
    return v___x_1361_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1362_ = leanh::lean_unsigned_to_nat(2);
    v___x_1363_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
    v___x_1364_ = l_Lean_Name_num___override(v___x_1363_, v___x_1362_);
    return v___x_1364_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: u8 = 0;
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_;
    v___x_1367_ = 0;
    v___x_1368_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
    v___x_1369_ = l_Lean_registerTraceClass(v___x_1366_, v___x_1367_, v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2____boxed(
    mut v_a_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1371_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_();
    return v_res_1371_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = leanh::lean_unsigned_to_nat(3083242752);
    v___x_1377_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1378_ = l_Lean_Name_num___override(v___x_1377_, v___x_1376_);
    return v___x_1378_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1380_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
    v___x_1381_ = l_Lean_Name_str___override(v___x_1380_, v___x_1379_);
    return v___x_1381_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1382_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1383_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
    v___x_1384_ = l_Lean_Name_str___override(v___x_1383_, v___x_1382_);
    return v___x_1384_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1385_ = leanh::lean_unsigned_to_nat(2);
    v___x_1386_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
    v___x_1387_ = l_Lean_Name_num___override(v___x_1386_, v___x_1385_);
    return v___x_1387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_;
    v___x_1390_ = 0;
    v___x_1391_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
    v___x_1392_ = l_Lean_registerTraceClass(v___x_1389_, v___x_1390_, v___x_1391_);
    return v___x_1392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2____boxed(
    mut v_a_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1394_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_();
    return v_res_1394_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = leanh::lean_unsigned_to_nat(2490045716);
    v___x_1401_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1402_ = l_Lean_Name_num___override(v___x_1401_, v___x_1400_);
    return v___x_1402_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1403_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1404_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
    v___x_1405_ = l_Lean_Name_str___override(v___x_1404_, v___x_1403_);
    return v___x_1405_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1407_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
    v___x_1408_ = l_Lean_Name_str___override(v___x_1407_, v___x_1406_);
    return v___x_1408_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = leanh::lean_unsigned_to_nat(2);
    v___x_1410_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
    v___x_1411_ = l_Lean_Name_num___override(v___x_1410_, v___x_1409_);
    return v___x_1411_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_;
    v___x_1414_ = 0;
    v___x_1415_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
    v___x_1416_ = l_Lean_registerTraceClass(v___x_1413_, v___x_1414_, v___x_1415_);
    return v___x_1416_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2____boxed(
    mut v_a_1417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_();
    return v_res_1418_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_;
    v___x_1438_ = 0;
    v___x_1439_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_;
    v___x_1440_ = l_Lean_registerTraceClass(v___x_1437_, v___x_1438_, v___x_1439_);
    return v___x_1440_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2____boxed(
    mut v_a_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1442_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_();
    return v_res_1442_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: u8 = 0;
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_;
    v___x_1463_ = 0;
    v___x_1464_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_;
    v___x_1465_ = l_Lean_registerTraceClass(v___x_1462_, v___x_1463_, v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2____boxed(
    mut v_a_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_();
    return v_res_1467_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = leanh::lean_unsigned_to_nat(3198151522);
    v___x_1475_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1476_ = l_Lean_Name_num___override(v___x_1475_, v___x_1474_);
    return v___x_1476_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1478_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
    v___x_1479_ = l_Lean_Name_str___override(v___x_1478_, v___x_1477_);
    return v___x_1479_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
    v___x_1482_ = l_Lean_Name_str___override(v___x_1481_, v___x_1480_);
    return v___x_1482_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = leanh::lean_unsigned_to_nat(2);
    v___x_1484_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
    v___x_1485_ = l_Lean_Name_num___override(v___x_1484_, v___x_1483_);
    return v___x_1485_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_;
    v___x_1488_ = 0;
    v___x_1489_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
    v___x_1490_ = l_Lean_registerTraceClass(v___x_1487_, v___x_1488_, v___x_1489_);
    return v___x_1490_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2____boxed(
    mut v_a_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1492_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_();
    return v_res_1492_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: u8 = 0;
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1510_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_;
    v___x_1511_ = 0;
    v___x_1512_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_;
    v___x_1513_ = l_Lean_registerTraceClass(v___x_1510_, v___x_1511_, v___x_1512_);
    return v___x_1513_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2____boxed(
    mut v_a_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_();
    return v_res_1515_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: u8 = 0;
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_;
    v___x_1534_ = 0;
    v___x_1535_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_;
    v___x_1536_ = l_Lean_registerTraceClass(v___x_1533_, v___x_1534_, v___x_1535_);
    return v___x_1536_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2____boxed(
    mut v_a_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1538_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_();
    return v_res_1538_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: u8 = 0;
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_;
    v___x_1557_ = 0;
    v___x_1558_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_;
    v___x_1559_ = l_Lean_registerTraceClass(v___x_1556_, v___x_1557_, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2____boxed(
    mut v_a_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_();
    return v_res_1561_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_;
    v___x_1581_ = 0;
    v___x_1582_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_;
    v___x_1583_ = l_Lean_registerTraceClass(v___x_1580_, v___x_1581_, v___x_1582_);
    return v___x_1583_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2____boxed(
    mut v_a_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1585_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_();
    return v_res_1585_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = leanh::lean_unsigned_to_nat(2208804552);
    v___x_1592_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1593_ = l_Lean_Name_num___override(v___x_1592_, v___x_1591_);
    return v___x_1593_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1595_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
    v___x_1596_ = l_Lean_Name_str___override(v___x_1595_, v___x_1594_);
    return v___x_1596_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1598_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
    v___x_1599_ = l_Lean_Name_str___override(v___x_1598_, v___x_1597_);
    return v___x_1599_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = leanh::lean_unsigned_to_nat(2);
    v___x_1601_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
    v___x_1602_ = l_Lean_Name_num___override(v___x_1601_, v___x_1600_);
    return v___x_1602_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1604_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_;
    v___x_1605_ = 0;
    v___x_1606_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
    v___x_1607_ = l_Lean_registerTraceClass(v___x_1604_, v___x_1605_, v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2____boxed(
    mut v_a_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_();
    return v_res_1609_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = leanh::lean_unsigned_to_nat(2239554481);
    v___x_1615_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1616_ = l_Lean_Name_num___override(v___x_1615_, v___x_1614_);
    return v___x_1616_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1618_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
    v___x_1619_ = l_Lean_Name_str___override(v___x_1618_, v___x_1617_);
    return v___x_1619_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1621_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
    v___x_1622_ = l_Lean_Name_str___override(v___x_1621_, v___x_1620_);
    return v___x_1622_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = leanh::lean_unsigned_to_nat(2);
    v___x_1624_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
    v___x_1625_ = l_Lean_Name_num___override(v___x_1624_, v___x_1623_);
    return v___x_1625_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_;
    v___x_1628_ = 0;
    v___x_1629_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
    v___x_1630_ = l_Lean_registerTraceClass(v___x_1627_, v___x_1628_, v___x_1629_);
    return v___x_1630_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2____boxed(
    mut v_a_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1632_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_();
    return v_res_1632_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ = leanh::lean_unsigned_to_nat(2451788450);
    v___x_1638_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1639_ = l_Lean_Name_num___override(v___x_1638_, v___x_1637_);
    return v___x_1639_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1641_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
    v___x_1642_ = l_Lean_Name_str___override(v___x_1641_, v___x_1640_);
    return v___x_1642_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1643_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1644_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
    v___x_1645_ = l_Lean_Name_str___override(v___x_1644_, v___x_1643_);
    return v___x_1645_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = leanh::lean_unsigned_to_nat(2);
    v___x_1647_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
    v___x_1648_ = l_Lean_Name_num___override(v___x_1647_, v___x_1646_);
    return v___x_1648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: u8 = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1650_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_;
    v___x_1651_ = 0;
    v___x_1652_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
    v___x_1653_ = l_Lean_registerTraceClass(v___x_1650_, v___x_1651_, v___x_1652_);
    return v___x_1653_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2____boxed(
    mut v_a_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_();
    return v_res_1655_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = leanh::lean_unsigned_to_nat(3390734082);
    v___x_1661_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1662_ = l_Lean_Name_num___override(v___x_1661_, v___x_1660_);
    return v___x_1662_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1664_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
    v___x_1665_ = l_Lean_Name_str___override(v___x_1664_, v___x_1663_);
    return v___x_1665_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
    v___x_1668_ = l_Lean_Name_str___override(v___x_1667_, v___x_1666_);
    return v___x_1668_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = leanh::lean_unsigned_to_nat(2);
    v___x_1670_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
    v___x_1671_ = l_Lean_Name_num___override(v___x_1670_, v___x_1669_);
    return v___x_1671_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_;
    v___x_1674_ = 0;
    v___x_1675_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
    v___x_1676_ = l_Lean_registerTraceClass(v___x_1673_, v___x_1674_, v___x_1675_);
    return v___x_1676_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2____boxed(
    mut v_a_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_();
    return v_res_1678_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1696_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_;
    v___x_1697_ = 0;
    v___x_1698_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_;
    v___x_1699_ = l_Lean_registerTraceClass(v___x_1696_, v___x_1697_, v___x_1698_);
    return v___x_1699_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2____boxed(
    mut v_a_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_();
    return v_res_1701_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = leanh::lean_unsigned_to_nat(2167643761);
    v___x_1707_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1708_ = l_Lean_Name_num___override(v___x_1707_, v___x_1706_);
    return v___x_1708_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1709_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1710_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
    v___x_1711_ = l_Lean_Name_str___override(v___x_1710_, v___x_1709_);
    return v___x_1711_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1713_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
    v___x_1714_ = l_Lean_Name_str___override(v___x_1713_, v___x_1712_);
    return v___x_1714_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = leanh::lean_unsigned_to_nat(2);
    v___x_1716_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
    v___x_1717_ = l_Lean_Name_num___override(v___x_1716_, v___x_1715_);
    return v___x_1717_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_;
    v___x_1720_ = 0;
    v___x_1721_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
    v___x_1722_ = l_Lean_registerTraceClass(v___x_1719_, v___x_1720_, v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2____boxed(
    mut v_a_1723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1724_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_();
    return v_res_1724_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = leanh::lean_unsigned_to_nat(3035027224);
    v___x_1731_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1732_ = l_Lean_Name_num___override(v___x_1731_, v___x_1730_);
    return v___x_1732_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1733_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1734_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
    v___x_1735_ = l_Lean_Name_str___override(v___x_1734_, v___x_1733_);
    return v___x_1735_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1737_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
    v___x_1738_ = l_Lean_Name_str___override(v___x_1737_, v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = leanh::lean_unsigned_to_nat(2);
    v___x_1740_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
    v___x_1741_ = l_Lean_Name_num___override(v___x_1740_, v___x_1739_);
    return v___x_1741_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_;
    v___x_1744_ = 1;
    v___x_1745_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
    v___x_1746_ = l_Lean_registerTraceClass(v___x_1743_, v___x_1744_, v___x_1745_);
    return v___x_1746_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2____boxed(
    mut v_a_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1748_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_();
    return v_res_1748_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_;
    v___x_1768_ = 1;
    v___x_1769_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_;
    v___x_1770_ = l_Lean_registerTraceClass(v___x_1767_, v___x_1768_, v___x_1769_);
    return v___x_1770_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2____boxed(
    mut v_a_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1772_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_();
    return v_res_1772_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: u8 = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_;
    v___x_1791_ = 1;
    v___x_1792_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_;
    v___x_1793_ = l_Lean_registerTraceClass(v___x_1790_, v___x_1791_, v___x_1792_);
    return v___x_1793_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2____boxed(
    mut v_a_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_();
    return v_res_1795_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1803_ = leanh::lean_unsigned_to_nat(3832561742);
    v___x_1804_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1805_ = l_Lean_Name_num___override(v___x_1804_, v___x_1803_);
    return v___x_1805_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1807_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
    v___x_1808_ = l_Lean_Name_str___override(v___x_1807_, v___x_1806_);
    return v___x_1808_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
    v___x_1811_ = l_Lean_Name_str___override(v___x_1810_, v___x_1809_);
    return v___x_1811_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1812_ = leanh::lean_unsigned_to_nat(2);
    v___x_1813_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
    v___x_1814_ = l_Lean_Name_num___override(v___x_1813_, v___x_1812_);
    return v___x_1814_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_;
    v___x_1817_ = 0;
    v___x_1818_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
    v___x_1819_ = l_Lean_registerTraceClass(v___x_1816_, v___x_1817_, v___x_1818_);
    return v___x_1819_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2____boxed(
    mut v_a_1820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1821_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_();
    return v_res_1821_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = leanh::lean_unsigned_to_nat(4253340762);
    v___x_1827_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1828_ = l_Lean_Name_num___override(v___x_1827_, v___x_1826_);
    return v___x_1828_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1830_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
    v___x_1831_ = l_Lean_Name_str___override(v___x_1830_, v___x_1829_);
    return v___x_1831_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1832_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1833_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
    v___x_1834_ = l_Lean_Name_str___override(v___x_1833_, v___x_1832_);
    return v___x_1834_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = leanh::lean_unsigned_to_nat(2);
    v___x_1836_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
    v___x_1837_ = l_Lean_Name_num___override(v___x_1836_, v___x_1835_);
    return v___x_1837_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_;
    v___x_1840_ = 0;
    v___x_1841_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
    v___x_1842_ = l_Lean_registerTraceClass(v___x_1839_, v___x_1840_, v___x_1841_);
    return v___x_1842_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2____boxed(
    mut v_a_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1844_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_();
    return v_res_1844_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = leanh::lean_unsigned_to_nat(3209233474);
    v___x_1851_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1852_ = l_Lean_Name_num___override(v___x_1851_, v___x_1850_);
    return v___x_1852_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1854_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
    v___x_1855_ = l_Lean_Name_str___override(v___x_1854_, v___x_1853_);
    return v___x_1855_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1857_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
    v___x_1858_ = l_Lean_Name_str___override(v___x_1857_, v___x_1856_);
    return v___x_1858_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = leanh::lean_unsigned_to_nat(2);
    v___x_1860_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
    v___x_1861_ = l_Lean_Name_num___override(v___x_1860_, v___x_1859_);
    return v___x_1861_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_;
    v___x_1864_ = 0;
    v___x_1865_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
    v___x_1866_ = l_Lean_registerTraceClass(v___x_1863_, v___x_1864_, v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2____boxed(
    mut v_a_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1868_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_();
    return v_res_1868_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = leanh::lean_unsigned_to_nat(3765097528);
    v___x_1875_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1876_ = l_Lean_Name_num___override(v___x_1875_, v___x_1874_);
    return v___x_1876_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1878_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
    v___x_1879_ = l_Lean_Name_str___override(v___x_1878_, v___x_1877_);
    return v___x_1879_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1880_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1881_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
    v___x_1882_ = l_Lean_Name_str___override(v___x_1881_, v___x_1880_);
    return v___x_1882_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1883_ = leanh::lean_unsigned_to_nat(2);
    v___x_1884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
    v___x_1885_ = l_Lean_Name_num___override(v___x_1884_, v___x_1883_);
    return v___x_1885_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: u8 = 0;
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1887_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_;
    v___x_1888_ = 0;
    v___x_1889_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
    v___x_1890_ = l_Lean_registerTraceClass(v___x_1887_, v___x_1888_, v___x_1889_);
    return v___x_1890_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2____boxed(
    mut v_a_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1892_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_();
    return v_res_1892_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_;
    v___x_1912_ = 0;
    v___x_1913_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_;
    v___x_1914_ = l_Lean_registerTraceClass(v___x_1911_, v___x_1912_, v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2____boxed(
    mut v_a_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1916_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_();
    return v_res_1916_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: u8 = 0;
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_;
    v___x_1936_ = 0;
    v___x_1937_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_;
    v___x_1938_ = l_Lean_registerTraceClass(v___x_1935_, v___x_1936_, v___x_1937_);
    return v___x_1938_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2____boxed(
    mut v_a_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1940_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_();
    return v_res_1940_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = leanh::lean_unsigned_to_nat(2205948307);
    v___x_1947_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1948_ = l_Lean_Name_num___override(v___x_1947_, v___x_1946_);
    return v___x_1948_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1950_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
    v___x_1951_ = l_Lean_Name_str___override(v___x_1950_, v___x_1949_);
    return v___x_1951_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1953_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
    v___x_1954_ = l_Lean_Name_str___override(v___x_1953_, v___x_1952_);
    return v___x_1954_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1955_ = leanh::lean_unsigned_to_nat(2);
    v___x_1956_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
    v___x_1957_ = l_Lean_Name_num___override(v___x_1956_, v___x_1955_);
    return v___x_1957_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1959_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_;
    v___x_1960_ = 0;
    v___x_1961_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
    v___x_1962_ = l_Lean_registerTraceClass(v___x_1959_, v___x_1960_, v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2____boxed(
    mut v_a_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1964_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_();
    return v_res_1964_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1970_ = leanh::lean_unsigned_to_nat(3880289020);
    v___x_1971_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1972_ = l_Lean_Name_num___override(v___x_1971_, v___x_1970_);
    return v___x_1972_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1973_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1974_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
    v___x_1975_ = l_Lean_Name_str___override(v___x_1974_, v___x_1973_);
    return v___x_1975_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1976_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1977_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
    v___x_1978_ = l_Lean_Name_str___override(v___x_1977_, v___x_1976_);
    return v___x_1978_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1979_ = leanh::lean_unsigned_to_nat(2);
    v___x_1980_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
    v___x_1981_ = l_Lean_Name_num___override(v___x_1980_, v___x_1979_);
    return v___x_1981_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u8 = 0;
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_;
    v___x_1984_ = 0;
    v___x_1985_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
    v___x_1986_ = l_Lean_registerTraceClass(v___x_1983_, v___x_1984_, v___x_1985_);
    return v___x_1986_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2____boxed(
    mut v_a_1987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1988_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_();
    return v_res_1988_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = leanh::lean_unsigned_to_nat(3921417167);
    v___x_1995_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1996_ = l_Lean_Name_num___override(v___x_1995_, v___x_1994_);
    return v___x_1996_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_1998_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
    v___x_1999_ = l_Lean_Name_str___override(v___x_1998_, v___x_1997_);
    return v___x_1999_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2000_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2001_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
    v___x_2002_ = l_Lean_Name_str___override(v___x_2001_, v___x_2000_);
    return v___x_2002_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2003_ = leanh::lean_unsigned_to_nat(2);
    v___x_2004_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
    v___x_2005_ = l_Lean_Name_num___override(v___x_2004_, v___x_2003_);
    return v___x_2005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_;
    v___x_2008_ = 0;
    v___x_2009_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
    v___x_2010_ = l_Lean_registerTraceClass(v___x_2007_, v___x_2008_, v___x_2009_);
    return v___x_2010_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2____boxed(
    mut v_a_2011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2012_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_();
    return v_res_2012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_;
    v___x_2031_ = 0;
    v___x_2032_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_;
    v___x_2033_ = l_Lean_registerTraceClass(v___x_2030_, v___x_2031_, v___x_2032_);
    return v___x_2033_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2____boxed(
    mut v_a_2034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2035_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_();
    return v_res_2035_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2054_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_;
    v___x_2055_ = 0;
    v___x_2056_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_;
    v___x_2057_ = l_Lean_registerTraceClass(v___x_2054_, v___x_2055_, v___x_2056_);
    return v___x_2057_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2____boxed(
    mut v_a_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2059_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_();
    return v_res_2059_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2080_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_;
    v___x_2081_ = 0;
    v___x_2082_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_;
    v___x_2083_ = l_Lean_registerTraceClass(v___x_2080_, v___x_2081_, v___x_2082_);
    return v___x_2083_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2____boxed(
    mut v_a_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2085_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_();
    return v_res_2085_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2091_ = leanh::lean_unsigned_to_nat(3036382584);
    v___x_2092_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2093_ = l_Lean_Name_num___override(v___x_2092_, v___x_2091_);
    return v___x_2093_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2094_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2095_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
    v___x_2096_ = l_Lean_Name_str___override(v___x_2095_, v___x_2094_);
    return v___x_2096_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2098_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
    v___x_2099_ = l_Lean_Name_str___override(v___x_2098_, v___x_2097_);
    return v___x_2099_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2100_ = leanh::lean_unsigned_to_nat(2);
    v___x_2101_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
    v___x_2102_ = l_Lean_Name_num___override(v___x_2101_, v___x_2100_);
    return v___x_2102_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: u8 = 0;
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_;
    v___x_2105_ = 0;
    v___x_2106_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
    v___x_2107_ = l_Lean_registerTraceClass(v___x_2104_, v___x_2105_, v___x_2106_);
    return v___x_2107_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2____boxed(
    mut v_a_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2109_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_();
    return v_res_2109_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2114_ = leanh::lean_unsigned_to_nat(3129348886);
    v___x_2115_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2116_ = l_Lean_Name_num___override(v___x_2115_, v___x_2114_);
    return v___x_2116_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2118_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
    v___x_2119_ = l_Lean_Name_str___override(v___x_2118_, v___x_2117_);
    return v___x_2119_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2120_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2121_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
    v___x_2122_ = l_Lean_Name_str___override(v___x_2121_, v___x_2120_);
    return v___x_2122_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = leanh::lean_unsigned_to_nat(2);
    v___x_2124_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
    v___x_2125_ = l_Lean_Name_num___override(v___x_2124_, v___x_2123_);
    return v___x_2125_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2127_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_;
    v___x_2128_ = 0;
    v___x_2129_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
    v___x_2130_ = l_Lean_registerTraceClass(v___x_2127_, v___x_2128_, v___x_2129_);
    return v___x_2130_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2____boxed(
    mut v_a_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2132_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_();
    return v_res_2132_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = leanh::lean_unsigned_to_nat(4094675293);
    v___x_2138_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2139_ = l_Lean_Name_num___override(v___x_2138_, v___x_2137_);
    return v___x_2139_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2141_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
    v___x_2142_ = l_Lean_Name_str___override(v___x_2141_, v___x_2140_);
    return v___x_2142_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2144_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
    v___x_2145_ = l_Lean_Name_str___override(v___x_2144_, v___x_2143_);
    return v___x_2145_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = leanh::lean_unsigned_to_nat(2);
    v___x_2147_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
    v___x_2148_ = l_Lean_Name_num___override(v___x_2147_, v___x_2146_);
    return v___x_2148_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2150_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_;
    v___x_2151_ = 0;
    v___x_2152_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
    v___x_2153_ = l_Lean_registerTraceClass(v___x_2150_, v___x_2151_, v___x_2152_);
    return v___x_2153_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2____boxed(
    mut v_a_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2155_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_();
    return v_res_2155_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2174_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_;
    v___x_2175_ = 0;
    v___x_2176_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_;
    v___x_2177_ = l_Lean_registerTraceClass(v___x_2174_, v___x_2175_, v___x_2176_);
    return v___x_2177_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2____boxed(
    mut v_a_2178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2179_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_();
    return v_res_2179_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_;
    v___x_2200_ = 0;
    v___x_2201_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_;
    v___x_2202_ = l_Lean_registerTraceClass(v___x_2199_, v___x_2200_, v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2____boxed(
    mut v_a_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2204_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_();
    return v_res_2204_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2211_ = leanh::lean_unsigned_to_nat(2833612631);
    v___x_2212_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2213_ = l_Lean_Name_num___override(v___x_2212_, v___x_2211_);
    return v___x_2213_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2215_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
    v___x_2216_ = l_Lean_Name_str___override(v___x_2215_, v___x_2214_);
    return v___x_2216_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2218_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
    v___x_2219_ = l_Lean_Name_str___override(v___x_2218_, v___x_2217_);
    return v___x_2219_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ = leanh::lean_unsigned_to_nat(2);
    v___x_2221_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
    v___x_2222_ = l_Lean_Name_num___override(v___x_2221_, v___x_2220_);
    return v___x_2222_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2224_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_;
    v___x_2225_ = 0;
    v___x_2226_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
    v___x_2227_ = l_Lean_registerTraceClass(v___x_2224_, v___x_2225_, v___x_2226_);
    return v___x_2227_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2____boxed(
    mut v_a_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2229_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_();
    return v_res_2229_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2234_ = leanh::lean_unsigned_to_nat(3357376128);
    v___x_2235_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2236_ = l_Lean_Name_num___override(v___x_2235_, v___x_2234_);
    return v___x_2236_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2238_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
    v___x_2239_ = l_Lean_Name_str___override(v___x_2238_, v___x_2237_);
    return v___x_2239_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2241_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
    v___x_2242_ = l_Lean_Name_str___override(v___x_2241_, v___x_2240_);
    return v___x_2242_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = leanh::lean_unsigned_to_nat(2);
    v___x_2244_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
    v___x_2245_ = l_Lean_Name_num___override(v___x_2244_, v___x_2243_);
    return v___x_2245_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: u8 = 0;
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2247_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_;
    v___x_2248_ = 0;
    v___x_2249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
    v___x_2250_ = l_Lean_registerTraceClass(v___x_2247_, v___x_2248_, v___x_2249_);
    return v___x_2250_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2____boxed(
    mut v_a_2251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_();
    return v_res_2252_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2270_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_;
    v___x_2271_ = 0;
    v___x_2272_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_;
    v___x_2273_ = l_Lean_registerTraceClass(v___x_2270_, v___x_2271_, v___x_2272_);
    return v___x_2273_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2____boxed(
    mut v_a_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2275_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_();
    return v_res_2275_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2281_ = leanh::lean_unsigned_to_nat(3746484445);
    v___x_2282_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2283_ = l_Lean_Name_num___override(v___x_2282_, v___x_2281_);
    return v___x_2283_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2284_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2285_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
    v___x_2286_ = l_Lean_Name_str___override(v___x_2285_, v___x_2284_);
    return v___x_2286_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2287_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2288_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
    v___x_2289_ = l_Lean_Name_str___override(v___x_2288_, v___x_2287_);
    return v___x_2289_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2290_ = leanh::lean_unsigned_to_nat(2);
    v___x_2291_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
    v___x_2292_ = l_Lean_Name_num___override(v___x_2291_, v___x_2290_);
    return v___x_2292_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_;
    v___x_2295_ = 0;
    v___x_2296_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
    v___x_2297_ = l_Lean_registerTraceClass(v___x_2294_, v___x_2295_, v___x_2296_);
    return v___x_2297_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2____boxed(
    mut v_a_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2299_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_();
    return v_res_2299_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = leanh::lean_unsigned_to_nat(4104889296);
    v___x_2306_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2307_ = l_Lean_Name_num___override(v___x_2306_, v___x_2305_);
    return v___x_2307_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2309_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
    v___x_2310_ = l_Lean_Name_str___override(v___x_2309_, v___x_2308_);
    return v___x_2310_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2311_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2312_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
    v___x_2313_ = l_Lean_Name_str___override(v___x_2312_, v___x_2311_);
    return v___x_2313_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ = leanh::lean_unsigned_to_nat(2);
    v___x_2315_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
    v___x_2316_ = l_Lean_Name_num___override(v___x_2315_, v___x_2314_);
    return v___x_2316_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2318_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_;
    v___x_2319_ = 0;
    v___x_2320_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
    v___x_2321_ = l_Lean_registerTraceClass(v___x_2318_, v___x_2319_, v___x_2320_);
    return v___x_2321_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2____boxed(
    mut v_a_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2323_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_();
    return v_res_2323_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = leanh::lean_unsigned_to_nat(3575722790);
    v___x_2330_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2331_ = l_Lean_Name_num___override(v___x_2330_, v___x_2329_);
    return v___x_2331_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2332_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2333_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
    v___x_2334_ = l_Lean_Name_str___override(v___x_2333_, v___x_2332_);
    return v___x_2334_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2336_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
    v___x_2337_ = l_Lean_Name_str___override(v___x_2336_, v___x_2335_);
    return v___x_2337_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = leanh::lean_unsigned_to_nat(2);
    v___x_2339_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
    v___x_2340_ = l_Lean_Name_num___override(v___x_2339_, v___x_2338_);
    return v___x_2340_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_;
    v___x_2343_ = 0;
    v___x_2344_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
    v___x_2345_ = l_Lean_registerTraceClass(v___x_2342_, v___x_2343_, v___x_2344_);
    return v___x_2345_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2____boxed(
    mut v_a_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2347_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_();
    return v_res_2347_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2365_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_;
    v___x_2366_ = 0;
    v___x_2367_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_;
    v___x_2368_ = l_Lean_registerTraceClass(v___x_2365_, v___x_2366_, v___x_2367_);
    return v___x_2368_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2____boxed(
    mut v_a_2369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2370_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_();
    return v_res_2370_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = leanh::lean_unsigned_to_nat(2489964793);
    v___x_2377_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2378_ = l_Lean_Name_num___override(v___x_2377_, v___x_2376_);
    return v___x_2378_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2379_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2380_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
    v___x_2381_ = l_Lean_Name_str___override(v___x_2380_, v___x_2379_);
    return v___x_2381_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2383_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
    v___x_2384_ = l_Lean_Name_str___override(v___x_2383_, v___x_2382_);
    return v___x_2384_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = leanh::lean_unsigned_to_nat(2);
    v___x_2386_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
    v___x_2387_ = l_Lean_Name_num___override(v___x_2386_, v___x_2385_);
    return v___x_2387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2389_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_;
    v___x_2390_ = 0;
    v___x_2391_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
    v___x_2392_ = l_Lean_registerTraceClass(v___x_2389_, v___x_2390_, v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2____boxed(
    mut v_a_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2394_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_();
    return v_res_2394_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2400_ = leanh::lean_unsigned_to_nat(2691769277);
    v___x_2401_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2402_ = l_Lean_Name_num___override(v___x_2401_, v___x_2400_);
    return v___x_2402_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2403_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2404_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
    v___x_2405_ = l_Lean_Name_str___override(v___x_2404_, v___x_2403_);
    return v___x_2405_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_;
    v___x_2407_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
    v___x_2408_ = l_Lean_Name_str___override(v___x_2407_, v___x_2406_);
    return v___x_2408_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2409_ = leanh::lean_unsigned_to_nat(2);
    v___x_2410_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
    v___x_2411_ = l_Lean_Name_num___override(v___x_2410_, v___x_2409_);
    return v___x_2411_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: u8 = 0;
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2413_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_;
    v___x_2414_ = 0;
    v___x_2415_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
    v___x_2416_ = l_Lean_registerTraceClass(v___x_2413_, v___x_2414_, v___x_2415_);
    return v___x_2416_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2____boxed(
    mut v_a_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_();
    return v_res_2418_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Propagate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Propagate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind(builtin);
}