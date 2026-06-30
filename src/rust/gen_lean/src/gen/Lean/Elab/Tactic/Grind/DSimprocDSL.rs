// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.DSimprocDSL
// Imports: Lean.Elab.Tactic.Grind.Basic Lean.Meta.Sym.DSimp Init.Sym.DSimp.DSimprocDSL
use crate::ffi::lean_st_ref_get;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getKind, l_Lean_replaceRef};
use crate::r#gen::Init::Sym::DSimp::DSimprocDSL::{
    initialize_Init_Sym_DSimp_DSimprocDSL, runtime_initialize_Init_Sym_DSimp_DSimprocDSL,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Grind::Basic::{
    initialize_Lean_Elab_Tactic_Grind_Basic, l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg,
    l_Lean_Elab_Tactic_Grind_saveState___redArg, runtime_initialize_Lean_Elab_Tactic_Grind_Basic,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_mkElabAttribute___redArg;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_getEntries___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::DSimp::{
    initialize_Lean_Meta_Sym_DSimp, runtime_initialize_Lean_Meta_Sym_DSimp,
};
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 121, 109, 95, 100, 115, 105, 109, 112, 114, 111, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9231270048838042427 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 121, 109, 95, 100, 115, 105, 109, 112, 114, 111, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3020423846782789775 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [68, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14634483482441683967 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [83, 121, 109, 68, 83, 105, 109, 112, 114, 111, 99, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5682547549171639295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10795475584547262066 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [115, 121, 109, 68, 83, 105, 109, 112, 114, 111, 99, 69, 108, 97, 98, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5682547549171639295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12915990776420102474 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__0_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 115, 121, 109, 95, 100, 115,
        105, 109, 112, 114, 111, 99, 32, 115, 121, 110, 116, 97, 120, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_400_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_;
    v___x_401_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_;
    v___x_402_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_;
    v___x_403_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_;
    v___x_404_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_;
    v___x_405_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_;
    v___x_406_ = l_Lean_Elab_mkElabAttribute___redArg(
        v___x_400_, v___x_402_, v___x_403_, v___x_404_, v___x_401_, v___x_405_,
    );
    return v___x_406_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2____boxed(
    mut v_a_407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_408_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_();
    return v_res_408_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2(
    mut v_msgData_409_: *mut leanh::LeanObject,
    mut v___y_410_: *mut leanh::LeanObject,
    mut v___y_411_: *mut leanh::LeanObject,
    mut v___y_412_: *mut leanh::LeanObject,
    mut v___y_413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = lean_st_ref_get(v___y_413_);
    v_env_416_ = leanh::lean_ctor_get(v___x_415_, 0);
    leanh::lean_inc_ref(v_env_416_);
    leanh::lean_dec(v___x_415_);
    v___x_417_ = lean_st_ref_get(v___y_411_);
    v_mctx_418_ = leanh::lean_ctor_get(v___x_417_, 0);
    leanh::lean_inc_ref(v_mctx_418_);
    leanh::lean_dec(v___x_417_);
    v_lctx_419_ = leanh::lean_ctor_get(v___y_410_, 2);
    v_options_420_ = leanh::lean_ctor_get(v___y_412_, 2);
    leanh::lean_inc_ref(v_options_420_);
    leanh::lean_inc_ref(v_lctx_419_);
    v___x_421_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_421_, 0, v_env_416_);
    leanh::lean_ctor_set(v___x_421_, 1, v_mctx_418_);
    leanh::lean_ctor_set(v___x_421_, 2, v_lctx_419_);
    leanh::lean_ctor_set(v___x_421_, 3, v_options_420_);
    v___x_422_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_422_, 0, v___x_421_);
    leanh::lean_ctor_set(v___x_422_, 1, v_msgData_409_);
    v___x_423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_423_, 0, v___x_422_);
    return v___x_423_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_424_: *mut leanh::LeanObject,
    mut v___y_425_: *mut leanh::LeanObject,
    mut v___y_426_: *mut leanh::LeanObject,
    mut v___y_427_: *mut leanh::LeanObject,
    mut v___y_428_: *mut leanh::LeanObject,
    mut v___y_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2(v_msgData_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
    leanh::lean_dec(v___y_428_);
    leanh::lean_dec_ref(v___y_427_);
    leanh::lean_dec(v___y_426_);
    leanh::lean_dec_ref(v___y_425_);
    return v_res_430_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(
    mut v_msg_431_: *mut leanh::LeanObject,
    mut v___y_432_: *mut leanh::LeanObject,
    mut v___y_433_: *mut leanh::LeanObject,
    mut v___y_434_: *mut leanh::LeanObject,
    mut v___y_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_442_: u8 = 0;
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_437_ = leanh::lean_ctor_get(v___y_434_, 5);
                v___x_438_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2(v_msg_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
                v_a_439_ = leanh::lean_ctor_get(v___x_438_, 0);
                v_isSharedCheck_447_ = (!leanh::lean_is_exclusive(v___x_438_)) as u8;
                if v_isSharedCheck_447_ == 0 {
                    v___x_441_ = v___x_438_;
                    v_isShared_442_ = v_isSharedCheck_447_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_439_);
                    leanh::lean_dec(v___x_438_);
                    v___x_441_ = leanh::lean_box(0);
                    v_isShared_442_ = v_isSharedCheck_447_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_437_);
                v___x_443_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_443_, 0, v_ref_437_);
                leanh::lean_ctor_set(v___x_443_, 1, v_a_439_);
                if v_isShared_442_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_441_, 1);
                    leanh::lean_ctor_set(v___x_441_, 0, v___x_443_);
                    v___x_445_ = v___x_441_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_446_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
                    v___x_445_ = v_reuseFailAlloc_446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg___boxed(
    mut v_msg_448_: *mut leanh::LeanObject,
    mut v___y_449_: *mut leanh::LeanObject,
    mut v___y_450_: *mut leanh::LeanObject,
    mut v___y_451_: *mut leanh::LeanObject,
    mut v___y_452_: *mut leanh::LeanObject,
    mut v___y_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_454_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(v_msg_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
    leanh::lean_dec(v___y_452_);
    leanh::lean_dec_ref(v___y_451_);
    leanh::lean_dec(v___y_450_);
    leanh::lean_dec_ref(v___y_449_);
    return v_res_454_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(
    mut v_ref_455_: *mut leanh::LeanObject,
    mut v_msg_456_: *mut leanh::LeanObject,
    mut v___y_457_: *mut leanh::LeanObject,
    mut v___y_458_: *mut leanh::LeanObject,
    mut v___y_459_: *mut leanh::LeanObject,
    mut v___y_460_: *mut leanh::LeanObject,
    mut v___y_461_: *mut leanh::LeanObject,
    mut v___y_462_: *mut leanh::LeanObject,
    mut v___y_463_: *mut leanh::LeanObject,
    mut v___y_464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_478_: u8 = 0;
    let mut v_cancelTk_x3f_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_480_: u8 = 0;
    let mut v_inheritedTraceOptions_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_466_ = leanh::lean_ctor_get(v___y_463_, 0);
    v_fileMap_467_ = leanh::lean_ctor_get(v___y_463_, 1);
    v_options_468_ = leanh::lean_ctor_get(v___y_463_, 2);
    v_currRecDepth_469_ = leanh::lean_ctor_get(v___y_463_, 3);
    v_maxRecDepth_470_ = leanh::lean_ctor_get(v___y_463_, 4);
    v_ref_471_ = leanh::lean_ctor_get(v___y_463_, 5);
    v_currNamespace_472_ = leanh::lean_ctor_get(v___y_463_, 6);
    v_openDecls_473_ = leanh::lean_ctor_get(v___y_463_, 7);
    v_initHeartbeats_474_ = leanh::lean_ctor_get(v___y_463_, 8);
    v_maxHeartbeats_475_ = leanh::lean_ctor_get(v___y_463_, 9);
    v_quotContext_476_ = leanh::lean_ctor_get(v___y_463_, 10);
    v_currMacroScope_477_ = leanh::lean_ctor_get(v___y_463_, 11);
    v_diag_478_ = leanh::lean_ctor_get_uint8(
        v___y_463_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_479_ = leanh::lean_ctor_get(v___y_463_, 12);
    v_suppressElabErrors_480_ = leanh::lean_ctor_get_uint8(
        v___y_463_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_481_ = leanh::lean_ctor_get(v___y_463_, 13);
    v_ref_482_ = l_Lean_replaceRef(v_ref_455_, v_ref_471_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_481_);
    leanh::lean_inc(v_cancelTk_x3f_479_);
    leanh::lean_inc(v_currMacroScope_477_);
    leanh::lean_inc(v_quotContext_476_);
    leanh::lean_inc(v_maxHeartbeats_475_);
    leanh::lean_inc(v_initHeartbeats_474_);
    leanh::lean_inc(v_openDecls_473_);
    leanh::lean_inc(v_currNamespace_472_);
    leanh::lean_inc(v_maxRecDepth_470_);
    leanh::lean_inc(v_currRecDepth_469_);
    leanh::lean_inc_ref(v_options_468_);
    leanh::lean_inc_ref(v_fileMap_467_);
    leanh::lean_inc_ref(v_fileName_466_);
    v___x_483_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_483_, 0, v_fileName_466_);
    leanh::lean_ctor_set(v___x_483_, 1, v_fileMap_467_);
    leanh::lean_ctor_set(v___x_483_, 2, v_options_468_);
    leanh::lean_ctor_set(v___x_483_, 3, v_currRecDepth_469_);
    leanh::lean_ctor_set(v___x_483_, 4, v_maxRecDepth_470_);
    leanh::lean_ctor_set(v___x_483_, 5, v_ref_482_);
    leanh::lean_ctor_set(v___x_483_, 6, v_currNamespace_472_);
    leanh::lean_ctor_set(v___x_483_, 7, v_openDecls_473_);
    leanh::lean_ctor_set(v___x_483_, 8, v_initHeartbeats_474_);
    leanh::lean_ctor_set(v___x_483_, 9, v_maxHeartbeats_475_);
    leanh::lean_ctor_set(v___x_483_, 10, v_quotContext_476_);
    leanh::lean_ctor_set(v___x_483_, 11, v_currMacroScope_477_);
    leanh::lean_ctor_set(v___x_483_, 12, v_cancelTk_x3f_479_);
    leanh::lean_ctor_set(v___x_483_, 13, v_inheritedTraceOptions_481_);
    leanh::lean_ctor_set_uint8(
        v___x_483_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_478_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_483_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_480_,
    );
    v___x_484_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(v_msg_456_, v___y_461_, v___y_462_, v___x_483_, v___y_464_);
    leanh::lean_dec_ref_known(v___x_483_, 14);
    return v___x_484_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg___boxed(
    mut v_ref_485_: *mut leanh::LeanObject,
    mut v_msg_486_: *mut leanh::LeanObject,
    mut v___y_487_: *mut leanh::LeanObject,
    mut v___y_488_: *mut leanh::LeanObject,
    mut v___y_489_: *mut leanh::LeanObject,
    mut v___y_490_: *mut leanh::LeanObject,
    mut v___y_491_: *mut leanh::LeanObject,
    mut v___y_492_: *mut leanh::LeanObject,
    mut v___y_493_: *mut leanh::LeanObject,
    mut v___y_494_: *mut leanh::LeanObject,
    mut v___y_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_496_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(
            v_ref_485_, v_msg_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_,
            v___y_492_, v___y_493_, v___y_494_,
        );
    leanh::lean_dec(v___y_494_);
    leanh::lean_dec_ref(v___y_493_);
    leanh::lean_dec(v___y_492_);
    leanh::lean_dec_ref(v___y_491_);
    leanh::lean_dec(v___y_490_);
    leanh::lean_dec_ref(v___y_489_);
    leanh::lean_dec(v___y_488_);
    leanh::lean_dec_ref(v___y_487_);
    leanh::lean_dec(v_ref_485_);
    return v_res_496_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(
    mut v_stx_500_: *mut leanh::LeanObject,
    mut v_as_x27_501_: *mut leanh::LeanObject,
    mut v_b_502_: *mut leanh::LeanObject,
    mut v___y_503_: *mut leanh::LeanObject,
    mut v___y_504_: *mut leanh::LeanObject,
    mut v___y_505_: *mut leanh::LeanObject,
    mut v___y_506_: *mut leanh::LeanObject,
    mut v___y_507_: *mut leanh::LeanObject,
    mut v___y_508_: *mut leanh::LeanObject,
    mut v___y_509_: *mut leanh::LeanObject,
    mut v___y_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_523_: u8 = 0;
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_529_: u8 = 0;
    let mut v_a_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_533_: u8 = 0;
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_536_: u8 = 0;
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_540_: u8 = 0;
    let mut v_id_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_551_: u8 = 0;
    let mut v_unused_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_560_: u8 = 0;
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: u8 = 0;
    let mut v___x_565_: u8 = 0;
    let mut v_isSharedCheck_566_: u8 = 0;
    let mut v_a_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_570_: u8 = 0;
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_501_) == 0 {
                    leanh::lean_dec(v_stx_500_);
                    v___x_512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_512_, 0, v_b_502_);
                    return v___x_512_;
                } else {
                    leanh::lean_dec_ref(v_b_502_);
                    v_head_513_ = leanh::lean_ctor_get(v_as_x27_501_, 0);
                    v_tail_514_ = leanh::lean_ctor_get(v_as_x27_501_, 1);
                    v___x_515_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(
                        v___y_504_, v___y_506_, v___y_508_, v___y_510_,
                    );
                    if leanh::lean_obj_tag(v___x_515_) == 0 {
                        v_a_516_ = leanh::lean_ctor_get(v___x_515_, 0);
                        leanh::lean_inc(v_a_516_);
                        leanh::lean_dec_ref_known(v___x_515_, 1);
                        v_value_517_ = leanh::lean_ctor_get(v_head_513_, 1);
                        v___x_518_ = leanh::lean_box(0);
                        leanh::lean_inc(v_value_517_);
                        leanh::lean_inc(v___y_510_);
                        leanh::lean_inc_ref(v___y_509_);
                        leanh::lean_inc(v___y_508_);
                        leanh::lean_inc_ref(v___y_507_);
                        leanh::lean_inc(v___y_506_);
                        leanh::lean_inc_ref(v___y_505_);
                        leanh::lean_inc(v___y_504_);
                        leanh::lean_inc_ref(v___y_503_);
                        leanh::lean_inc(v_stx_500_);
                        v___x_519_ = leanh::lean_apply_10(
                            v_value_517_,
                            v_stx_500_,
                            v___y_503_,
                            v___y_504_,
                            v___y_505_,
                            v___y_506_,
                            v___y_507_,
                            v___y_508_,
                            v___y_509_,
                            v___y_510_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_519_) == 0 {
                            leanh::lean_dec(v_a_516_);
                            leanh::lean_dec(v_stx_500_);
                            v_a_520_ = leanh::lean_ctor_get(v___x_519_, 0);
                            v_isSharedCheck_529_ =
                                (!leanh::lean_is_exclusive(v___x_519_)) as u8;
                            if v_isSharedCheck_529_ == 0 {
                                v___x_522_ = v___x_519_;
                                v_isShared_523_ = v_isSharedCheck_529_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_520_);
                                leanh::lean_dec(v___x_519_);
                                v___x_522_ = leanh::lean_box(0);
                                v_isShared_523_ = v_isSharedCheck_529_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_530_ = leanh::lean_ctor_get(v___x_519_, 0);
                            v_isSharedCheck_566_ =
                                (!leanh::lean_is_exclusive(v___x_519_)) as u8;
                            if v_isSharedCheck_566_ == 0 {
                                v___x_532_ = v___x_519_;
                                v_isShared_533_ = v_isSharedCheck_566_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_530_);
                                leanh::lean_dec(v___x_519_);
                                v___x_532_ = leanh::lean_box(0);
                                v_isShared_533_ = v_isSharedCheck_566_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_stx_500_);
                        v_a_567_ = leanh::lean_ctor_get(v___x_515_, 0);
                        v_isSharedCheck_574_ = (!leanh::lean_is_exclusive(v___x_515_)) as u8;
                        if v_isSharedCheck_574_ == 0 {
                            v___x_569_ = v___x_515_;
                            v_isShared_570_ = v_isSharedCheck_574_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_567_);
                            leanh::lean_dec(v___x_515_);
                            v___x_569_ = leanh::lean_box(0);
                            v_isShared_570_ = v_isSharedCheck_574_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_524_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_524_, 0, v_a_520_);
                v___x_525_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_525_, 0, v___x_524_);
                leanh::lean_ctor_set(v___x_525_, 1, v___x_518_);
                if v_isShared_523_ == 0 {
                    leanh::lean_ctor_set(v___x_522_, 0, v___x_525_);
                    v___x_527_ = v___x_522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_528_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
                    v___x_527_ = v_reuseFailAlloc_528_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_527_;
            }
            3 => {
                v___x_534_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0;
                v___x_564_ = l_Lean_Exception_isInterrupt(v_a_530_);
                if v___x_564_ == 0 {
                    leanh::lean_inc(v_a_530_);
                    v___x_565_ = l_Lean_Exception_isRuntime(v_a_530_);
                    v___y_536_ = v___x_565_;
                    state = 4;
                    continue;
                } else {
                    v___y_536_ = v___x_564_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_536_ == 0 {
                    leanh::lean_del_object(v___x_532_);
                    v___x_537_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(
                        v_a_516_, v___y_536_, v___y_504_, v___y_505_, v___y_506_, v___y_507_,
                        v___y_508_, v___y_509_, v___y_510_,
                    );
                    if leanh::lean_obj_tag(v___x_537_) == 0 {
                        v_isSharedCheck_551_ = (!leanh::lean_is_exclusive(v___x_537_)) as u8;
                        if v_isSharedCheck_551_ == 0 {
                            v_unused_552_ = leanh::lean_ctor_get(v___x_537_, 0);
                            leanh::lean_dec(v_unused_552_);
                            v___x_539_ = v___x_537_;
                            v_isShared_540_ = v_isSharedCheck_551_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_537_);
                            v___x_539_ = leanh::lean_box(0);
                            v_isShared_540_ = v_isSharedCheck_551_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_530_);
                        leanh::lean_dec(v_stx_500_);
                        v_a_553_ = leanh::lean_ctor_get(v___x_537_, 0);
                        v_isSharedCheck_560_ = (!leanh::lean_is_exclusive(v___x_537_)) as u8;
                        if v_isSharedCheck_560_ == 0 {
                            v___x_555_ = v___x_537_;
                            v_isShared_556_ = v_isSharedCheck_560_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_553_);
                            leanh::lean_dec(v___x_537_);
                            v___x_555_ = leanh::lean_box(0);
                            v_isShared_556_ = v_isSharedCheck_560_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_516_);
                    leanh::lean_dec(v_stx_500_);
                    if v_isShared_533_ == 0 {
                        v___x_562_ = v___x_532_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_563_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_530_);
                        v___x_562_ = v_reuseFailAlloc_563_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_530_) == 1 {
                    v_id_541_ = leanh::lean_ctor_get(v_a_530_, 0);
                    v___x_542_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_543_ = l_Lean_instBEqInternalExceptionId_beq(v_id_541_, v___x_542_);
                    if v___x_543_ == 0 {
                        leanh::lean_dec(v_stx_500_);
                        if v_isShared_540_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_539_, 1);
                            leanh::lean_ctor_set(v___x_539_, 0, v_a_530_);
                            v___x_545_ = v___x_539_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_546_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_530_);
                            v___x_545_ = v_reuseFailAlloc_546_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_530_, 2);
                        leanh::lean_del_object(v___x_539_);
                        v_as_x27_501_ = v_tail_514_;
                        v_b_502_ = v___x_534_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_stx_500_);
                    if v_isShared_540_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_539_, 1);
                        leanh::lean_ctor_set(v___x_539_, 0, v_a_530_);
                        v___x_549_ = v___x_539_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_550_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_530_);
                        v___x_549_ = v_reuseFailAlloc_550_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_545_;
            }
            7 => {
                return v___x_549_;
            }
            8 => {
                if v_isShared_556_ == 0 {
                    v___x_558_ = v___x_555_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
                    v___x_558_ = v_reuseFailAlloc_559_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_558_;
            }
            10 => {
                return v___x_562_;
            }
            11 => {
                if v_isShared_570_ == 0 {
                    v___x_572_ = v___x_569_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_573_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
                    v___x_572_ = v_reuseFailAlloc_573_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___boxed(
    mut v_stx_575_: *mut leanh::LeanObject,
    mut v_as_x27_576_: *mut leanh::LeanObject,
    mut v_b_577_: *mut leanh::LeanObject,
    mut v___y_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
    mut v___y_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
    mut v___y_584_: *mut leanh::LeanObject,
    mut v___y_585_: *mut leanh::LeanObject,
    mut v___y_586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_587_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(
            v_stx_575_,
            v_as_x27_576_,
            v_b_577_,
            v___y_578_,
            v___y_579_,
            v___y_580_,
            v___y_581_,
            v___y_582_,
            v___y_583_,
            v___y_584_,
            v___y_585_,
        );
    leanh::lean_dec(v___y_585_);
    leanh::lean_dec_ref(v___y_584_);
    leanh::lean_dec(v___y_583_);
    leanh::lean_dec_ref(v___y_582_);
    leanh::lean_dec(v___y_581_);
    leanh::lean_dec_ref(v___y_580_);
    leanh::lean_dec(v___y_579_);
    leanh::lean_dec_ref(v___y_578_);
    leanh::lean_dec(v_as_x27_576_);
    return v_res_587_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__0;
    v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
    return v___x_590_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__2;
    v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
    return v___x_593_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabSymDSimproc(
    mut v_stx_594_: *mut leanh::LeanObject,
    mut v_a_595_: *mut leanh::LeanObject,
    mut v_a_596_: *mut leanh::LeanObject,
    mut v_a_597_: *mut leanh::LeanObject,
    mut v_a_598_: *mut leanh::LeanObject,
    mut v_a_599_: *mut leanh::LeanObject,
    mut v_a_600_: *mut leanh::LeanObject,
    mut v_a_601_: *mut leanh::LeanObject,
    mut v_a_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_614_: u8 = 0;
    let mut v_fst_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_618_: u8 = 0;
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v_unused_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut v_a_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_637_: u8 = 0;
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_604_ = lean_st_ref_get(v_a_602_);
                v_env_605_ = leanh::lean_ctor_get(v___x_604_, 0);
                leanh::lean_inc_ref(v_env_605_);
                leanh::lean_dec(v___x_604_);
                v___x_606_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
                leanh::lean_inc_n(v_stx_594_, 2);
                v___x_607_ = l_Lean_Syntax_getKind(v_stx_594_);
                v___x_608_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(
                    v___x_606_, v_env_605_, v___x_607_,
                );
                v___x_609_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0;
                v___x_610_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(v_stx_594_, v___x_608_, v___x_609_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
                leanh::lean_dec(v___x_608_);
                if leanh::lean_obj_tag(v___x_610_) == 0 {
                    v_a_611_ = leanh::lean_ctor_get(v___x_610_, 0);
                    v_isSharedCheck_633_ = (!leanh::lean_is_exclusive(v___x_610_)) as u8;
                    if v_isSharedCheck_633_ == 0 {
                        v___x_613_ = v___x_610_;
                        v_isShared_614_ = v_isSharedCheck_633_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_611_);
                        leanh::lean_dec(v___x_610_);
                        v___x_613_ = leanh::lean_box(0);
                        v_isShared_614_ = v_isSharedCheck_633_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_607_);
                    leanh::lean_dec(v_stx_594_);
                    v_a_634_ = leanh::lean_ctor_get(v___x_610_, 0);
                    v_isSharedCheck_641_ = (!leanh::lean_is_exclusive(v___x_610_)) as u8;
                    if v_isSharedCheck_641_ == 0 {
                        v___x_636_ = v___x_610_;
                        v_isShared_637_ = v_isSharedCheck_641_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_634_);
                        leanh::lean_dec(v___x_610_);
                        v___x_636_ = leanh::lean_box(0);
                        v_isShared_637_ = v_isSharedCheck_641_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_615_ = leanh::lean_ctor_get(v_a_611_, 0);
                v_isSharedCheck_631_ = (!leanh::lean_is_exclusive(v_a_611_)) as u8;
                if v_isSharedCheck_631_ == 0 {
                    v_unused_632_ = leanh::lean_ctor_get(v_a_611_, 1);
                    leanh::lean_dec(v_unused_632_);
                    v___x_617_ = v_a_611_;
                    v_isShared_618_ = v_isSharedCheck_631_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_615_);
                    leanh::lean_dec(v_a_611_);
                    v___x_617_ = leanh::lean_box(0);
                    v_isShared_618_ = v_isSharedCheck_631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_615_) == 0 {
                    leanh::lean_del_object(v___x_613_);
                    v___x_619_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1,
                    );
                    v___x_620_ = l_Lean_MessageData_ofName(v___x_607_);
                    if v_isShared_618_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_617_, 7);
                        leanh::lean_ctor_set(v___x_617_, 1, v___x_620_);
                        leanh::lean_ctor_set(v___x_617_, 0, v___x_619_);
                        v___x_622_ = v___x_617_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_626_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_619_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_620_);
                        v___x_622_ = v_reuseFailAlloc_626_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_617_);
                    leanh::lean_dec(v___x_607_);
                    leanh::lean_dec(v_stx_594_);
                    v_val_627_ = leanh::lean_ctor_get(v_fst_615_, 0);
                    leanh::lean_inc(v_val_627_);
                    leanh::lean_dec_ref_known(v_fst_615_, 1);
                    if v_isShared_614_ == 0 {
                        leanh::lean_ctor_set(v___x_613_, 0, v_val_627_);
                        v___x_629_ = v___x_613_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_630_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v_val_627_);
                        v___x_629_ = v_reuseFailAlloc_630_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_623_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3_once
                    ),
                    _init_l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3,
                );
                v___x_624_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_624_, 0, v___x_622_);
                leanh::lean_ctor_set(v___x_624_, 1, v___x_623_);
                v___x_625_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(v_stx_594_, v___x_624_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
                leanh::lean_dec(v_stx_594_);
                return v___x_625_;
            }
            4 => {
                return v___x_629_;
            }
            5 => {
                if v_isShared_637_ == 0 {
                    v___x_639_ = v___x_636_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_640_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
                    v___x_639_ = v_reuseFailAlloc_640_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabSymDSimproc___boxed(
    mut v_stx_642_: *mut leanh::LeanObject,
    mut v_a_643_: *mut leanh::LeanObject,
    mut v_a_644_: *mut leanh::LeanObject,
    mut v_a_645_: *mut leanh::LeanObject,
    mut v_a_646_: *mut leanh::LeanObject,
    mut v_a_647_: *mut leanh::LeanObject,
    mut v_a_648_: *mut leanh::LeanObject,
    mut v_a_649_: *mut leanh::LeanObject,
    mut v_a_650_: *mut leanh::LeanObject,
    mut v_a_651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_652_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(
        v_stx_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_,
    );
    leanh::lean_dec(v_a_650_);
    leanh::lean_dec_ref(v_a_649_);
    leanh::lean_dec(v_a_648_);
    leanh::lean_dec_ref(v_a_647_);
    leanh::lean_dec(v_a_646_);
    leanh::lean_dec_ref(v_a_645_);
    leanh::lean_dec(v_a_644_);
    leanh::lean_dec_ref(v_a_643_);
    return v_res_652_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0(
    mut v_stx_653_: *mut leanh::LeanObject,
    mut v_as_654_: *mut leanh::LeanObject,
    mut v_as_x27_655_: *mut leanh::LeanObject,
    mut v_b_656_: *mut leanh::LeanObject,
    mut v_a_657_: *mut leanh::LeanObject,
    mut v___y_658_: *mut leanh::LeanObject,
    mut v___y_659_: *mut leanh::LeanObject,
    mut v___y_660_: *mut leanh::LeanObject,
    mut v___y_661_: *mut leanh::LeanObject,
    mut v___y_662_: *mut leanh::LeanObject,
    mut v___y_663_: *mut leanh::LeanObject,
    mut v___y_664_: *mut leanh::LeanObject,
    mut v___y_665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_667_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(
            v_stx_653_,
            v_as_x27_655_,
            v_b_656_,
            v___y_658_,
            v___y_659_,
            v___y_660_,
            v___y_661_,
            v___y_662_,
            v___y_663_,
            v___y_664_,
            v___y_665_,
        );
    return v___x_667_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___boxed(
    mut v_stx_668_: *mut leanh::LeanObject,
    mut v_as_669_: *mut leanh::LeanObject,
    mut v_as_x27_670_: *mut leanh::LeanObject,
    mut v_b_671_: *mut leanh::LeanObject,
    mut v_a_672_: *mut leanh::LeanObject,
    mut v___y_673_: *mut leanh::LeanObject,
    mut v___y_674_: *mut leanh::LeanObject,
    mut v___y_675_: *mut leanh::LeanObject,
    mut v___y_676_: *mut leanh::LeanObject,
    mut v___y_677_: *mut leanh::LeanObject,
    mut v___y_678_: *mut leanh::LeanObject,
    mut v___y_679_: *mut leanh::LeanObject,
    mut v___y_680_: *mut leanh::LeanObject,
    mut v___y_681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_682_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0(
        v_stx_668_,
        v_as_669_,
        v_as_x27_670_,
        v_b_671_,
        v_a_672_,
        v___y_673_,
        v___y_674_,
        v___y_675_,
        v___y_676_,
        v___y_677_,
        v___y_678_,
        v___y_679_,
        v___y_680_,
    );
    leanh::lean_dec(v___y_680_);
    leanh::lean_dec_ref(v___y_679_);
    leanh::lean_dec(v___y_678_);
    leanh::lean_dec_ref(v___y_677_);
    leanh::lean_dec(v___y_676_);
    leanh::lean_dec_ref(v___y_675_);
    leanh::lean_dec(v___y_674_);
    leanh::lean_dec_ref(v___y_673_);
    leanh::lean_dec(v_as_x27_670_);
    leanh::lean_dec(v_as_669_);
    return v_res_682_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1(
    mut v_00_u03b1_683_: *mut leanh::LeanObject,
    mut v_ref_684_: *mut leanh::LeanObject,
    mut v_msg_685_: *mut leanh::LeanObject,
    mut v___y_686_: *mut leanh::LeanObject,
    mut v___y_687_: *mut leanh::LeanObject,
    mut v___y_688_: *mut leanh::LeanObject,
    mut v___y_689_: *mut leanh::LeanObject,
    mut v___y_690_: *mut leanh::LeanObject,
    mut v___y_691_: *mut leanh::LeanObject,
    mut v___y_692_: *mut leanh::LeanObject,
    mut v___y_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(
            v_ref_684_, v_msg_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_,
            v___y_691_, v___y_692_, v___y_693_,
        );
    return v___x_695_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___boxed(
    mut v_00_u03b1_696_: *mut leanh::LeanObject,
    mut v_ref_697_: *mut leanh::LeanObject,
    mut v_msg_698_: *mut leanh::LeanObject,
    mut v___y_699_: *mut leanh::LeanObject,
    mut v___y_700_: *mut leanh::LeanObject,
    mut v___y_701_: *mut leanh::LeanObject,
    mut v___y_702_: *mut leanh::LeanObject,
    mut v___y_703_: *mut leanh::LeanObject,
    mut v___y_704_: *mut leanh::LeanObject,
    mut v___y_705_: *mut leanh::LeanObject,
    mut v___y_706_: *mut leanh::LeanObject,
    mut v___y_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_708_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1(
        v_00_u03b1_696_,
        v_ref_697_,
        v_msg_698_,
        v___y_699_,
        v___y_700_,
        v___y_701_,
        v___y_702_,
        v___y_703_,
        v___y_704_,
        v___y_705_,
        v___y_706_,
    );
    leanh::lean_dec(v___y_706_);
    leanh::lean_dec_ref(v___y_705_);
    leanh::lean_dec(v___y_704_);
    leanh::lean_dec_ref(v___y_703_);
    leanh::lean_dec(v___y_702_);
    leanh::lean_dec_ref(v___y_701_);
    leanh::lean_dec(v___y_700_);
    leanh::lean_dec_ref(v___y_699_);
    leanh::lean_dec(v_ref_697_);
    return v_res_708_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1(
    mut v_00_u03b1_709_: *mut leanh::LeanObject,
    mut v_msg_710_: *mut leanh::LeanObject,
    mut v___y_711_: *mut leanh::LeanObject,
    mut v___y_712_: *mut leanh::LeanObject,
    mut v___y_713_: *mut leanh::LeanObject,
    mut v___y_714_: *mut leanh::LeanObject,
    mut v___y_715_: *mut leanh::LeanObject,
    mut v___y_716_: *mut leanh::LeanObject,
    mut v___y_717_: *mut leanh::LeanObject,
    mut v___y_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(v_msg_710_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
    return v___x_720_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___boxed(
    mut v_00_u03b1_721_: *mut leanh::LeanObject,
    mut v_msg_722_: *mut leanh::LeanObject,
    mut v___y_723_: *mut leanh::LeanObject,
    mut v___y_724_: *mut leanh::LeanObject,
    mut v___y_725_: *mut leanh::LeanObject,
    mut v___y_726_: *mut leanh::LeanObject,
    mut v___y_727_: *mut leanh::LeanObject,
    mut v___y_728_: *mut leanh::LeanObject,
    mut v___y_729_: *mut leanh::LeanObject,
    mut v___y_730_: *mut leanh::LeanObject,
    mut v___y_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_732_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1(v_00_u03b1_721_, v_msg_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
    leanh::lean_dec(v___y_730_);
    leanh::lean_dec_ref(v___y_729_);
    leanh::lean_dec(v___y_728_);
    leanh::lean_dec_ref(v___y_727_);
    leanh::lean_dec(v___y_726_);
    leanh::lean_dec_ref(v___y_725_);
    leanh::lean_dec(v___y_724_);
    leanh::lean_dec_ref(v___y_723_);
    return v_res_732_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
}