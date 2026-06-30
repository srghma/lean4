// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.SimprocDSL
// Imports: Lean.Elab.Tactic.Grind.Basic Lean.Meta.Sym.Simp.Discharger Init.Sym.Simp.SimprocDSL
use crate::ffi::lean_st_ref_get;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getKind, l_Lean_replaceRef};
use crate::r#gen::Init::Sym::Simp::SimprocDSL::{
    initialize_Init_Sym_Simp_SimprocDSL, runtime_initialize_Init_Sym_Simp_SimprocDSL,
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
use crate::r#gen::Lean::Meta::Sym::Simp::Discharger::{
    initialize_Lean_Meta_Sym_Simp_Discharger, runtime_initialize_Lean_Meta_Sym_Simp_Discharger,
};
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 121, 109, 95, 115, 105, 109, 112, 114, 111, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1213030753372943601 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 121, 109, 95, 115, 105, 109, 112, 114, 111, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17663670605732064950 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17473872748478919658 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17762876748869580590 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [83, 121, 109, 83, 105, 109, 112, 114, 111, 99, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5682547549171639295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12073567694863697409 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [115, 121, 109, 83, 105, 109, 112, 114, 111, 99, 69, 108, 97, 98, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5682547549171639295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5196301779119341153 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 115, 121, 109, 95, 100, 105, 115, 99, 104, 97, 114, 103, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5328030520468358913 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 121, 109, 95, 100, 105, 115, 99, 104, 97, 114, 103, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16913365718413729959 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 121, 109, 68, 105, 115, 99, 104, 97, 114, 103, 101, 114, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5682547549171639295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16946966980300773549 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [115, 121, 109, 68, 105, 115, 99, 104, 97, 114, 103, 101, 114, 69, 108, 97, 98, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5682547549171639295 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15271541544854744533 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__0_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 115, 121, 109, 95, 115, 105,
        109, 112, 114, 111, 99, 32, 115, 121, 110, 116, 97, 120, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__0_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 115, 121, 109, 95, 100, 105,
        115, 99, 104, 97, 114, 103, 101, 114, 32, 115, 121, 110, 116, 97, 120, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_613_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_;
    v___x_614_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_;
    v___x_615_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_;
    v___x_616_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_;
    v___x_617_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_;
    v___x_618_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_;
    v___x_619_ = l_Lean_Elab_mkElabAttribute___redArg(
        v___x_613_, v___x_615_, v___x_616_, v___x_617_, v___x_614_, v___x_618_,
    );
    return v___x_619_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2____boxed(
    mut v_a_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_();
    return v_res_621_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_;
    v___x_644_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_;
    v___x_645_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_;
    v___x_646_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_;
    v___x_647_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_;
    v___x_648_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_;
    v___x_649_ = l_Lean_Elab_mkElabAttribute___redArg(
        v___x_643_, v___x_645_, v___x_646_, v___x_647_, v___x_644_, v___x_648_,
    );
    return v___x_649_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2____boxed(
    mut v_a_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_651_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_();
    return v_res_651_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2(
    mut v_msgData_652_: *mut leanh::LeanObject,
    mut v___y_653_: *mut leanh::LeanObject,
    mut v___y_654_: *mut leanh::LeanObject,
    mut v___y_655_: *mut leanh::LeanObject,
    mut v___y_656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = lean_st_ref_get(v___y_656_);
    v_env_659_ = leanh::lean_ctor_get(v___x_658_, 0);
    leanh::lean_inc_ref(v_env_659_);
    leanh::lean_dec(v___x_658_);
    v___x_660_ = lean_st_ref_get(v___y_654_);
    v_mctx_661_ = leanh::lean_ctor_get(v___x_660_, 0);
    leanh::lean_inc_ref(v_mctx_661_);
    leanh::lean_dec(v___x_660_);
    v_lctx_662_ = leanh::lean_ctor_get(v___y_653_, 2);
    v_options_663_ = leanh::lean_ctor_get(v___y_655_, 2);
    leanh::lean_inc_ref(v_options_663_);
    leanh::lean_inc_ref(v_lctx_662_);
    v___x_664_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_664_, 0, v_env_659_);
    leanh::lean_ctor_set(v___x_664_, 1, v_mctx_661_);
    leanh::lean_ctor_set(v___x_664_, 2, v_lctx_662_);
    leanh::lean_ctor_set(v___x_664_, 3, v_options_663_);
    v___x_665_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_665_, 0, v___x_664_);
    leanh::lean_ctor_set(v___x_665_, 1, v_msgData_652_);
    v___x_666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_666_, 0, v___x_665_);
    return v___x_666_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_667_: *mut leanh::LeanObject,
    mut v___y_668_: *mut leanh::LeanObject,
    mut v___y_669_: *mut leanh::LeanObject,
    mut v___y_670_: *mut leanh::LeanObject,
    mut v___y_671_: *mut leanh::LeanObject,
    mut v___y_672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_673_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2(v_msgData_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
    leanh::lean_dec(v___y_671_);
    leanh::lean_dec_ref(v___y_670_);
    leanh::lean_dec(v___y_669_);
    leanh::lean_dec_ref(v___y_668_);
    return v_res_673_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(
    mut v_msg_674_: *mut leanh::LeanObject,
    mut v___y_675_: *mut leanh::LeanObject,
    mut v___y_676_: *mut leanh::LeanObject,
    mut v___y_677_: *mut leanh::LeanObject,
    mut v___y_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_685_: u8 = 0;
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_690_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_680_ = leanh::lean_ctor_get(v___y_677_, 5);
                v___x_681_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2(v_msg_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
                v_a_682_ = leanh::lean_ctor_get(v___x_681_, 0);
                v_isSharedCheck_690_ = (!leanh::lean_is_exclusive(v___x_681_)) as u8;
                if v_isSharedCheck_690_ == 0 {
                    v___x_684_ = v___x_681_;
                    v_isShared_685_ = v_isSharedCheck_690_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_682_);
                    leanh::lean_dec(v___x_681_);
                    v___x_684_ = leanh::lean_box(0);
                    v_isShared_685_ = v_isSharedCheck_690_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_680_);
                v___x_686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_686_, 0, v_ref_680_);
                leanh::lean_ctor_set(v___x_686_, 1, v_a_682_);
                if v_isShared_685_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_684_, 1);
                    leanh::lean_ctor_set(v___x_684_, 0, v___x_686_);
                    v___x_688_ = v___x_684_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_689_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
                    v___x_688_ = v_reuseFailAlloc_689_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg___boxed(
    mut v_msg_691_: *mut leanh::LeanObject,
    mut v___y_692_: *mut leanh::LeanObject,
    mut v___y_693_: *mut leanh::LeanObject,
    mut v___y_694_: *mut leanh::LeanObject,
    mut v___y_695_: *mut leanh::LeanObject,
    mut v___y_696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_697_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(v_msg_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
    leanh::lean_dec(v___y_695_);
    leanh::lean_dec_ref(v___y_694_);
    leanh::lean_dec(v___y_693_);
    leanh::lean_dec_ref(v___y_692_);
    return v_res_697_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(
    mut v_ref_698_: *mut leanh::LeanObject,
    mut v_msg_699_: *mut leanh::LeanObject,
    mut v___y_700_: *mut leanh::LeanObject,
    mut v___y_701_: *mut leanh::LeanObject,
    mut v___y_702_: *mut leanh::LeanObject,
    mut v___y_703_: *mut leanh::LeanObject,
    mut v___y_704_: *mut leanh::LeanObject,
    mut v___y_705_: *mut leanh::LeanObject,
    mut v___y_706_: *mut leanh::LeanObject,
    mut v___y_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_721_: u8 = 0;
    let mut v_cancelTk_x3f_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_723_: u8 = 0;
    let mut v_inheritedTraceOptions_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_709_ = leanh::lean_ctor_get(v___y_706_, 0);
    v_fileMap_710_ = leanh::lean_ctor_get(v___y_706_, 1);
    v_options_711_ = leanh::lean_ctor_get(v___y_706_, 2);
    v_currRecDepth_712_ = leanh::lean_ctor_get(v___y_706_, 3);
    v_maxRecDepth_713_ = leanh::lean_ctor_get(v___y_706_, 4);
    v_ref_714_ = leanh::lean_ctor_get(v___y_706_, 5);
    v_currNamespace_715_ = leanh::lean_ctor_get(v___y_706_, 6);
    v_openDecls_716_ = leanh::lean_ctor_get(v___y_706_, 7);
    v_initHeartbeats_717_ = leanh::lean_ctor_get(v___y_706_, 8);
    v_maxHeartbeats_718_ = leanh::lean_ctor_get(v___y_706_, 9);
    v_quotContext_719_ = leanh::lean_ctor_get(v___y_706_, 10);
    v_currMacroScope_720_ = leanh::lean_ctor_get(v___y_706_, 11);
    v_diag_721_ = leanh::lean_ctor_get_uint8(
        v___y_706_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_722_ = leanh::lean_ctor_get(v___y_706_, 12);
    v_suppressElabErrors_723_ = leanh::lean_ctor_get_uint8(
        v___y_706_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_724_ = leanh::lean_ctor_get(v___y_706_, 13);
    v_ref_725_ = l_Lean_replaceRef(v_ref_698_, v_ref_714_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_724_);
    leanh::lean_inc(v_cancelTk_x3f_722_);
    leanh::lean_inc(v_currMacroScope_720_);
    leanh::lean_inc(v_quotContext_719_);
    leanh::lean_inc(v_maxHeartbeats_718_);
    leanh::lean_inc(v_initHeartbeats_717_);
    leanh::lean_inc(v_openDecls_716_);
    leanh::lean_inc(v_currNamespace_715_);
    leanh::lean_inc(v_maxRecDepth_713_);
    leanh::lean_inc(v_currRecDepth_712_);
    leanh::lean_inc_ref(v_options_711_);
    leanh::lean_inc_ref(v_fileMap_710_);
    leanh::lean_inc_ref(v_fileName_709_);
    v___x_726_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_726_, 0, v_fileName_709_);
    leanh::lean_ctor_set(v___x_726_, 1, v_fileMap_710_);
    leanh::lean_ctor_set(v___x_726_, 2, v_options_711_);
    leanh::lean_ctor_set(v___x_726_, 3, v_currRecDepth_712_);
    leanh::lean_ctor_set(v___x_726_, 4, v_maxRecDepth_713_);
    leanh::lean_ctor_set(v___x_726_, 5, v_ref_725_);
    leanh::lean_ctor_set(v___x_726_, 6, v_currNamespace_715_);
    leanh::lean_ctor_set(v___x_726_, 7, v_openDecls_716_);
    leanh::lean_ctor_set(v___x_726_, 8, v_initHeartbeats_717_);
    leanh::lean_ctor_set(v___x_726_, 9, v_maxHeartbeats_718_);
    leanh::lean_ctor_set(v___x_726_, 10, v_quotContext_719_);
    leanh::lean_ctor_set(v___x_726_, 11, v_currMacroScope_720_);
    leanh::lean_ctor_set(v___x_726_, 12, v_cancelTk_x3f_722_);
    leanh::lean_ctor_set(v___x_726_, 13, v_inheritedTraceOptions_724_);
    leanh::lean_ctor_set_uint8(
        v___x_726_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_721_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_726_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_723_,
    );
    v___x_727_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(v_msg_699_, v___y_704_, v___y_705_, v___x_726_, v___y_707_);
    leanh::lean_dec_ref_known(v___x_726_, 14);
    return v___x_727_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg___boxed(
    mut v_ref_728_: *mut leanh::LeanObject,
    mut v_msg_729_: *mut leanh::LeanObject,
    mut v___y_730_: *mut leanh::LeanObject,
    mut v___y_731_: *mut leanh::LeanObject,
    mut v___y_732_: *mut leanh::LeanObject,
    mut v___y_733_: *mut leanh::LeanObject,
    mut v___y_734_: *mut leanh::LeanObject,
    mut v___y_735_: *mut leanh::LeanObject,
    mut v___y_736_: *mut leanh::LeanObject,
    mut v___y_737_: *mut leanh::LeanObject,
    mut v___y_738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_739_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(
            v_ref_728_, v_msg_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_,
            v___y_735_, v___y_736_, v___y_737_,
        );
    leanh::lean_dec(v___y_737_);
    leanh::lean_dec_ref(v___y_736_);
    leanh::lean_dec(v___y_735_);
    leanh::lean_dec_ref(v___y_734_);
    leanh::lean_dec(v___y_733_);
    leanh::lean_dec_ref(v___y_732_);
    leanh::lean_dec(v___y_731_);
    leanh::lean_dec_ref(v___y_730_);
    leanh::lean_dec(v_ref_728_);
    return v_res_739_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(
    mut v_stx_743_: *mut leanh::LeanObject,
    mut v_as_x27_744_: *mut leanh::LeanObject,
    mut v_b_745_: *mut leanh::LeanObject,
    mut v___y_746_: *mut leanh::LeanObject,
    mut v___y_747_: *mut leanh::LeanObject,
    mut v___y_748_: *mut leanh::LeanObject,
    mut v___y_749_: *mut leanh::LeanObject,
    mut v___y_750_: *mut leanh::LeanObject,
    mut v___y_751_: *mut leanh::LeanObject,
    mut v___y_752_: *mut leanh::LeanObject,
    mut v___y_753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_766_: u8 = 0;
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_772_: u8 = 0;
    let mut v_a_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_776_: u8 = 0;
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_779_: u8 = 0;
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_783_: u8 = 0;
    let mut v_id_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: u8 = 0;
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut v_unused_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: u8 = 0;
    let mut v_isSharedCheck_809_: u8 = 0;
    let mut v_a_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_813_: u8 = 0;
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_744_) == 0 {
                    leanh::lean_dec(v_stx_743_);
                    v___x_755_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_755_, 0, v_b_745_);
                    return v___x_755_;
                } else {
                    leanh::lean_dec_ref(v_b_745_);
                    v_head_756_ = leanh::lean_ctor_get(v_as_x27_744_, 0);
                    v_tail_757_ = leanh::lean_ctor_get(v_as_x27_744_, 1);
                    v___x_758_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(
                        v___y_747_, v___y_749_, v___y_751_, v___y_753_,
                    );
                    if leanh::lean_obj_tag(v___x_758_) == 0 {
                        v_a_759_ = leanh::lean_ctor_get(v___x_758_, 0);
                        leanh::lean_inc(v_a_759_);
                        leanh::lean_dec_ref_known(v___x_758_, 1);
                        v_value_760_ = leanh::lean_ctor_get(v_head_756_, 1);
                        v___x_761_ = leanh::lean_box(0);
                        leanh::lean_inc(v_value_760_);
                        leanh::lean_inc(v___y_753_);
                        leanh::lean_inc_ref(v___y_752_);
                        leanh::lean_inc(v___y_751_);
                        leanh::lean_inc_ref(v___y_750_);
                        leanh::lean_inc(v___y_749_);
                        leanh::lean_inc_ref(v___y_748_);
                        leanh::lean_inc(v___y_747_);
                        leanh::lean_inc_ref(v___y_746_);
                        leanh::lean_inc(v_stx_743_);
                        v___x_762_ = leanh::lean_apply_10(
                            v_value_760_,
                            v_stx_743_,
                            v___y_746_,
                            v___y_747_,
                            v___y_748_,
                            v___y_749_,
                            v___y_750_,
                            v___y_751_,
                            v___y_752_,
                            v___y_753_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_762_) == 0 {
                            leanh::lean_dec(v_a_759_);
                            leanh::lean_dec(v_stx_743_);
                            v_a_763_ = leanh::lean_ctor_get(v___x_762_, 0);
                            v_isSharedCheck_772_ =
                                (!leanh::lean_is_exclusive(v___x_762_)) as u8;
                            if v_isSharedCheck_772_ == 0 {
                                v___x_765_ = v___x_762_;
                                v_isShared_766_ = v_isSharedCheck_772_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_763_);
                                leanh::lean_dec(v___x_762_);
                                v___x_765_ = leanh::lean_box(0);
                                v_isShared_766_ = v_isSharedCheck_772_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_773_ = leanh::lean_ctor_get(v___x_762_, 0);
                            v_isSharedCheck_809_ =
                                (!leanh::lean_is_exclusive(v___x_762_)) as u8;
                            if v_isSharedCheck_809_ == 0 {
                                v___x_775_ = v___x_762_;
                                v_isShared_776_ = v_isSharedCheck_809_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_773_);
                                leanh::lean_dec(v___x_762_);
                                v___x_775_ = leanh::lean_box(0);
                                v_isShared_776_ = v_isSharedCheck_809_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_stx_743_);
                        v_a_810_ = leanh::lean_ctor_get(v___x_758_, 0);
                        v_isSharedCheck_817_ = (!leanh::lean_is_exclusive(v___x_758_)) as u8;
                        if v_isSharedCheck_817_ == 0 {
                            v___x_812_ = v___x_758_;
                            v_isShared_813_ = v_isSharedCheck_817_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_810_);
                            leanh::lean_dec(v___x_758_);
                            v___x_812_ = leanh::lean_box(0);
                            v_isShared_813_ = v_isSharedCheck_817_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_767_, 0, v_a_763_);
                v___x_768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_768_, 0, v___x_767_);
                leanh::lean_ctor_set(v___x_768_, 1, v___x_761_);
                if v_isShared_766_ == 0 {
                    leanh::lean_ctor_set(v___x_765_, 0, v___x_768_);
                    v___x_770_ = v___x_765_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
                    v___x_770_ = v_reuseFailAlloc_771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_770_;
            }
            3 => {
                v___x_777_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0;
                v___x_807_ = l_Lean_Exception_isInterrupt(v_a_773_);
                if v___x_807_ == 0 {
                    leanh::lean_inc(v_a_773_);
                    v___x_808_ = l_Lean_Exception_isRuntime(v_a_773_);
                    v___y_779_ = v___x_808_;
                    state = 4;
                    continue;
                } else {
                    v___y_779_ = v___x_807_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_779_ == 0 {
                    leanh::lean_del_object(v___x_775_);
                    v___x_780_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(
                        v_a_759_, v___y_779_, v___y_747_, v___y_748_, v___y_749_, v___y_750_,
                        v___y_751_, v___y_752_, v___y_753_,
                    );
                    if leanh::lean_obj_tag(v___x_780_) == 0 {
                        v_isSharedCheck_794_ = (!leanh::lean_is_exclusive(v___x_780_)) as u8;
                        if v_isSharedCheck_794_ == 0 {
                            v_unused_795_ = leanh::lean_ctor_get(v___x_780_, 0);
                            leanh::lean_dec(v_unused_795_);
                            v___x_782_ = v___x_780_;
                            v_isShared_783_ = v_isSharedCheck_794_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_780_);
                            v___x_782_ = leanh::lean_box(0);
                            v_isShared_783_ = v_isSharedCheck_794_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_773_);
                        leanh::lean_dec(v_stx_743_);
                        v_a_796_ = leanh::lean_ctor_get(v___x_780_, 0);
                        v_isSharedCheck_803_ = (!leanh::lean_is_exclusive(v___x_780_)) as u8;
                        if v_isSharedCheck_803_ == 0 {
                            v___x_798_ = v___x_780_;
                            v_isShared_799_ = v_isSharedCheck_803_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_796_);
                            leanh::lean_dec(v___x_780_);
                            v___x_798_ = leanh::lean_box(0);
                            v_isShared_799_ = v_isSharedCheck_803_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_759_);
                    leanh::lean_dec(v_stx_743_);
                    if v_isShared_776_ == 0 {
                        v___x_805_ = v___x_775_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_773_);
                        v___x_805_ = v_reuseFailAlloc_806_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_773_) == 1 {
                    v_id_784_ = leanh::lean_ctor_get(v_a_773_, 0);
                    v___x_785_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_786_ = l_Lean_instBEqInternalExceptionId_beq(v_id_784_, v___x_785_);
                    if v___x_786_ == 0 {
                        leanh::lean_dec(v_stx_743_);
                        if v_isShared_783_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_782_, 1);
                            leanh::lean_ctor_set(v___x_782_, 0, v_a_773_);
                            v___x_788_ = v___x_782_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_773_);
                            v___x_788_ = v_reuseFailAlloc_789_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_773_, 2);
                        leanh::lean_del_object(v___x_782_);
                        v_as_x27_744_ = v_tail_757_;
                        v_b_745_ = v___x_777_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_stx_743_);
                    if v_isShared_783_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_782_, 1);
                        leanh::lean_ctor_set(v___x_782_, 0, v_a_773_);
                        v___x_792_ = v___x_782_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_793_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_773_);
                        v___x_792_ = v_reuseFailAlloc_793_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_788_;
            }
            7 => {
                return v___x_792_;
            }
            8 => {
                if v_isShared_799_ == 0 {
                    v___x_801_ = v___x_798_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
                    v___x_801_ = v_reuseFailAlloc_802_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_801_;
            }
            10 => {
                return v___x_805_;
            }
            11 => {
                if v_isShared_813_ == 0 {
                    v___x_815_ = v___x_812_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
                    v___x_815_ = v_reuseFailAlloc_816_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___boxed(
    mut v_stx_818_: *mut leanh::LeanObject,
    mut v_as_x27_819_: *mut leanh::LeanObject,
    mut v_b_820_: *mut leanh::LeanObject,
    mut v___y_821_: *mut leanh::LeanObject,
    mut v___y_822_: *mut leanh::LeanObject,
    mut v___y_823_: *mut leanh::LeanObject,
    mut v___y_824_: *mut leanh::LeanObject,
    mut v___y_825_: *mut leanh::LeanObject,
    mut v___y_826_: *mut leanh::LeanObject,
    mut v___y_827_: *mut leanh::LeanObject,
    mut v___y_828_: *mut leanh::LeanObject,
    mut v___y_829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_830_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(
            v_stx_818_,
            v_as_x27_819_,
            v_b_820_,
            v___y_821_,
            v___y_822_,
            v___y_823_,
            v___y_824_,
            v___y_825_,
            v___y_826_,
            v___y_827_,
            v___y_828_,
        );
    leanh::lean_dec(v___y_828_);
    leanh::lean_dec_ref(v___y_827_);
    leanh::lean_dec(v___y_826_);
    leanh::lean_dec_ref(v___y_825_);
    leanh::lean_dec(v___y_824_);
    leanh::lean_dec_ref(v___y_823_);
    leanh::lean_dec(v___y_822_);
    leanh::lean_dec_ref(v___y_821_);
    leanh::lean_dec(v_as_x27_819_);
    return v_res_830_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__0;
    v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
    return v___x_833_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__2;
    v___x_836_ = l_Lean_stringToMessageData(v___x_835_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabSymSimproc(
    mut v_stx_837_: *mut leanh::LeanObject,
    mut v_a_838_: *mut leanh::LeanObject,
    mut v_a_839_: *mut leanh::LeanObject,
    mut v_a_840_: *mut leanh::LeanObject,
    mut v_a_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
    mut v_a_844_: *mut leanh::LeanObject,
    mut v_a_845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_857_: u8 = 0;
    let mut v_fst_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_861_: u8 = 0;
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v_unused_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut v_a_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_880_: u8 = 0;
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_847_ = lean_st_ref_get(v_a_845_);
                v_env_848_ = leanh::lean_ctor_get(v___x_847_, 0);
                leanh::lean_inc_ref(v_env_848_);
                leanh::lean_dec(v___x_847_);
                v___x_849_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
                leanh::lean_inc_n(v_stx_837_, 2);
                v___x_850_ = l_Lean_Syntax_getKind(v_stx_837_);
                v___x_851_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(
                    v___x_849_, v_env_848_, v___x_850_,
                );
                v___x_852_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0;
                v___x_853_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(v_stx_837_, v___x_851_, v___x_852_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
                leanh::lean_dec(v___x_851_);
                if leanh::lean_obj_tag(v___x_853_) == 0 {
                    v_a_854_ = leanh::lean_ctor_get(v___x_853_, 0);
                    v_isSharedCheck_876_ = (!leanh::lean_is_exclusive(v___x_853_)) as u8;
                    if v_isSharedCheck_876_ == 0 {
                        v___x_856_ = v___x_853_;
                        v_isShared_857_ = v_isSharedCheck_876_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_854_);
                        leanh::lean_dec(v___x_853_);
                        v___x_856_ = leanh::lean_box(0);
                        v_isShared_857_ = v_isSharedCheck_876_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_850_);
                    leanh::lean_dec(v_stx_837_);
                    v_a_877_ = leanh::lean_ctor_get(v___x_853_, 0);
                    v_isSharedCheck_884_ = (!leanh::lean_is_exclusive(v___x_853_)) as u8;
                    if v_isSharedCheck_884_ == 0 {
                        v___x_879_ = v___x_853_;
                        v_isShared_880_ = v_isSharedCheck_884_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_877_);
                        leanh::lean_dec(v___x_853_);
                        v___x_879_ = leanh::lean_box(0);
                        v_isShared_880_ = v_isSharedCheck_884_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_858_ = leanh::lean_ctor_get(v_a_854_, 0);
                v_isSharedCheck_874_ = (!leanh::lean_is_exclusive(v_a_854_)) as u8;
                if v_isSharedCheck_874_ == 0 {
                    v_unused_875_ = leanh::lean_ctor_get(v_a_854_, 1);
                    leanh::lean_dec(v_unused_875_);
                    v___x_860_ = v_a_854_;
                    v_isShared_861_ = v_isSharedCheck_874_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_858_);
                    leanh::lean_dec(v_a_854_);
                    v___x_860_ = leanh::lean_box(0);
                    v_isShared_861_ = v_isSharedCheck_874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_858_) == 0 {
                    leanh::lean_del_object(v___x_856_);
                    v___x_862_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1,
                    );
                    v___x_863_ = l_Lean_MessageData_ofName(v___x_850_);
                    if v_isShared_861_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_860_, 7);
                        leanh::lean_ctor_set(v___x_860_, 1, v___x_863_);
                        leanh::lean_ctor_set(v___x_860_, 0, v___x_862_);
                        v___x_865_ = v___x_860_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_869_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_862_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_863_);
                        v___x_865_ = v_reuseFailAlloc_869_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_860_);
                    leanh::lean_dec(v___x_850_);
                    leanh::lean_dec(v_stx_837_);
                    v_val_870_ = leanh::lean_ctor_get(v_fst_858_, 0);
                    leanh::lean_inc(v_val_870_);
                    leanh::lean_dec_ref_known(v_fst_858_, 1);
                    if v_isShared_857_ == 0 {
                        leanh::lean_ctor_set(v___x_856_, 0, v_val_870_);
                        v___x_872_ = v___x_856_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_873_, 0, v_val_870_);
                        v___x_872_ = v_reuseFailAlloc_873_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_866_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3_once
                    ),
                    _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3,
                );
                v___x_867_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_867_, 0, v___x_865_);
                leanh::lean_ctor_set(v___x_867_, 1, v___x_866_);
                v___x_868_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(v_stx_837_, v___x_867_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
                leanh::lean_dec(v_stx_837_);
                return v___x_868_;
            }
            4 => {
                return v___x_872_;
            }
            5 => {
                if v_isShared_880_ == 0 {
                    v___x_882_ = v___x_879_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
                    v___x_882_ = v_reuseFailAlloc_883_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabSymSimproc___boxed(
    mut v_stx_885_: *mut leanh::LeanObject,
    mut v_a_886_: *mut leanh::LeanObject,
    mut v_a_887_: *mut leanh::LeanObject,
    mut v_a_888_: *mut leanh::LeanObject,
    mut v_a_889_: *mut leanh::LeanObject,
    mut v_a_890_: *mut leanh::LeanObject,
    mut v_a_891_: *mut leanh::LeanObject,
    mut v_a_892_: *mut leanh::LeanObject,
    mut v_a_893_: *mut leanh::LeanObject,
    mut v_a_894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(
        v_stx_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_,
    );
    leanh::lean_dec(v_a_893_);
    leanh::lean_dec_ref(v_a_892_);
    leanh::lean_dec(v_a_891_);
    leanh::lean_dec_ref(v_a_890_);
    leanh::lean_dec(v_a_889_);
    leanh::lean_dec_ref(v_a_888_);
    leanh::lean_dec(v_a_887_);
    leanh::lean_dec_ref(v_a_886_);
    return v_res_895_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0(
    mut v_stx_896_: *mut leanh::LeanObject,
    mut v_as_897_: *mut leanh::LeanObject,
    mut v_as_x27_898_: *mut leanh::LeanObject,
    mut v_b_899_: *mut leanh::LeanObject,
    mut v_a_900_: *mut leanh::LeanObject,
    mut v___y_901_: *mut leanh::LeanObject,
    mut v___y_902_: *mut leanh::LeanObject,
    mut v___y_903_: *mut leanh::LeanObject,
    mut v___y_904_: *mut leanh::LeanObject,
    mut v___y_905_: *mut leanh::LeanObject,
    mut v___y_906_: *mut leanh::LeanObject,
    mut v___y_907_: *mut leanh::LeanObject,
    mut v___y_908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(
            v_stx_896_,
            v_as_x27_898_,
            v_b_899_,
            v___y_901_,
            v___y_902_,
            v___y_903_,
            v___y_904_,
            v___y_905_,
            v___y_906_,
            v___y_907_,
            v___y_908_,
        );
    return v___x_910_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___boxed(
    mut v_stx_911_: *mut leanh::LeanObject,
    mut v_as_912_: *mut leanh::LeanObject,
    mut v_as_x27_913_: *mut leanh::LeanObject,
    mut v_b_914_: *mut leanh::LeanObject,
    mut v_a_915_: *mut leanh::LeanObject,
    mut v___y_916_: *mut leanh::LeanObject,
    mut v___y_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
    mut v___y_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
    mut v___y_921_: *mut leanh::LeanObject,
    mut v___y_922_: *mut leanh::LeanObject,
    mut v___y_923_: *mut leanh::LeanObject,
    mut v___y_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_925_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0(
        v_stx_911_,
        v_as_912_,
        v_as_x27_913_,
        v_b_914_,
        v_a_915_,
        v___y_916_,
        v___y_917_,
        v___y_918_,
        v___y_919_,
        v___y_920_,
        v___y_921_,
        v___y_922_,
        v___y_923_,
    );
    leanh::lean_dec(v___y_923_);
    leanh::lean_dec_ref(v___y_922_);
    leanh::lean_dec(v___y_921_);
    leanh::lean_dec_ref(v___y_920_);
    leanh::lean_dec(v___y_919_);
    leanh::lean_dec_ref(v___y_918_);
    leanh::lean_dec(v___y_917_);
    leanh::lean_dec_ref(v___y_916_);
    leanh::lean_dec(v_as_x27_913_);
    leanh::lean_dec(v_as_912_);
    return v_res_925_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1(
    mut v_00_u03b1_926_: *mut leanh::LeanObject,
    mut v_ref_927_: *mut leanh::LeanObject,
    mut v_msg_928_: *mut leanh::LeanObject,
    mut v___y_929_: *mut leanh::LeanObject,
    mut v___y_930_: *mut leanh::LeanObject,
    mut v___y_931_: *mut leanh::LeanObject,
    mut v___y_932_: *mut leanh::LeanObject,
    mut v___y_933_: *mut leanh::LeanObject,
    mut v___y_934_: *mut leanh::LeanObject,
    mut v___y_935_: *mut leanh::LeanObject,
    mut v___y_936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(
            v_ref_927_, v_msg_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_,
            v___y_934_, v___y_935_, v___y_936_,
        );
    return v___x_938_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___boxed(
    mut v_00_u03b1_939_: *mut leanh::LeanObject,
    mut v_ref_940_: *mut leanh::LeanObject,
    mut v_msg_941_: *mut leanh::LeanObject,
    mut v___y_942_: *mut leanh::LeanObject,
    mut v___y_943_: *mut leanh::LeanObject,
    mut v___y_944_: *mut leanh::LeanObject,
    mut v___y_945_: *mut leanh::LeanObject,
    mut v___y_946_: *mut leanh::LeanObject,
    mut v___y_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
    mut v___y_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_951_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1(
        v_00_u03b1_939_,
        v_ref_940_,
        v_msg_941_,
        v___y_942_,
        v___y_943_,
        v___y_944_,
        v___y_945_,
        v___y_946_,
        v___y_947_,
        v___y_948_,
        v___y_949_,
    );
    leanh::lean_dec(v___y_949_);
    leanh::lean_dec_ref(v___y_948_);
    leanh::lean_dec(v___y_947_);
    leanh::lean_dec_ref(v___y_946_);
    leanh::lean_dec(v___y_945_);
    leanh::lean_dec_ref(v___y_944_);
    leanh::lean_dec(v___y_943_);
    leanh::lean_dec_ref(v___y_942_);
    leanh::lean_dec(v_ref_940_);
    return v_res_951_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1(
    mut v_00_u03b1_952_: *mut leanh::LeanObject,
    mut v_msg_953_: *mut leanh::LeanObject,
    mut v___y_954_: *mut leanh::LeanObject,
    mut v___y_955_: *mut leanh::LeanObject,
    mut v___y_956_: *mut leanh::LeanObject,
    mut v___y_957_: *mut leanh::LeanObject,
    mut v___y_958_: *mut leanh::LeanObject,
    mut v___y_959_: *mut leanh::LeanObject,
    mut v___y_960_: *mut leanh::LeanObject,
    mut v___y_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(v_msg_953_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
    return v___x_963_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___boxed(
    mut v_00_u03b1_964_: *mut leanh::LeanObject,
    mut v_msg_965_: *mut leanh::LeanObject,
    mut v___y_966_: *mut leanh::LeanObject,
    mut v___y_967_: *mut leanh::LeanObject,
    mut v___y_968_: *mut leanh::LeanObject,
    mut v___y_969_: *mut leanh::LeanObject,
    mut v___y_970_: *mut leanh::LeanObject,
    mut v___y_971_: *mut leanh::LeanObject,
    mut v___y_972_: *mut leanh::LeanObject,
    mut v___y_973_: *mut leanh::LeanObject,
    mut v___y_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_975_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1(v_00_u03b1_964_, v_msg_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
    leanh::lean_dec(v___y_973_);
    leanh::lean_dec_ref(v___y_972_);
    leanh::lean_dec(v___y_971_);
    leanh::lean_dec_ref(v___y_970_);
    leanh::lean_dec(v___y_969_);
    leanh::lean_dec_ref(v___y_968_);
    leanh::lean_dec(v___y_967_);
    leanh::lean_dec_ref(v___y_966_);
    return v_res_975_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(
    mut v_stx_979_: *mut leanh::LeanObject,
    mut v_as_x27_980_: *mut leanh::LeanObject,
    mut v_b_981_: *mut leanh::LeanObject,
    mut v___y_982_: *mut leanh::LeanObject,
    mut v___y_983_: *mut leanh::LeanObject,
    mut v___y_984_: *mut leanh::LeanObject,
    mut v___y_985_: *mut leanh::LeanObject,
    mut v___y_986_: *mut leanh::LeanObject,
    mut v___y_987_: *mut leanh::LeanObject,
    mut v___y_988_: *mut leanh::LeanObject,
    mut v___y_989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v_a_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1012_: u8 = 0;
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1015_: u8 = 0;
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v_id_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: u8 = 0;
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1030_: u8 = 0;
    let mut v_unused_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1035_: u8 = 0;
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1039_: u8 = 0;
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    let mut v___x_1044_: u8 = 0;
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_a_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1049_: u8 = 0;
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1053_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_980_) == 0 {
                    leanh::lean_dec(v_stx_979_);
                    v___x_991_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_991_, 0, v_b_981_);
                    return v___x_991_;
                } else {
                    leanh::lean_dec_ref(v_b_981_);
                    v_head_992_ = leanh::lean_ctor_get(v_as_x27_980_, 0);
                    v_tail_993_ = leanh::lean_ctor_get(v_as_x27_980_, 1);
                    v___x_994_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(
                        v___y_983_, v___y_985_, v___y_987_, v___y_989_,
                    );
                    if leanh::lean_obj_tag(v___x_994_) == 0 {
                        v_a_995_ = leanh::lean_ctor_get(v___x_994_, 0);
                        leanh::lean_inc(v_a_995_);
                        leanh::lean_dec_ref_known(v___x_994_, 1);
                        v_value_996_ = leanh::lean_ctor_get(v_head_992_, 1);
                        v___x_997_ = leanh::lean_box(0);
                        leanh::lean_inc(v_value_996_);
                        leanh::lean_inc(v___y_989_);
                        leanh::lean_inc_ref(v___y_988_);
                        leanh::lean_inc(v___y_987_);
                        leanh::lean_inc_ref(v___y_986_);
                        leanh::lean_inc(v___y_985_);
                        leanh::lean_inc_ref(v___y_984_);
                        leanh::lean_inc(v___y_983_);
                        leanh::lean_inc_ref(v___y_982_);
                        leanh::lean_inc(v_stx_979_);
                        v___x_998_ = leanh::lean_apply_10(
                            v_value_996_,
                            v_stx_979_,
                            v___y_982_,
                            v___y_983_,
                            v___y_984_,
                            v___y_985_,
                            v___y_986_,
                            v___y_987_,
                            v___y_988_,
                            v___y_989_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_998_) == 0 {
                            leanh::lean_dec(v_a_995_);
                            leanh::lean_dec(v_stx_979_);
                            v_a_999_ = leanh::lean_ctor_get(v___x_998_, 0);
                            v_isSharedCheck_1008_ =
                                (!leanh::lean_is_exclusive(v___x_998_)) as u8;
                            if v_isSharedCheck_1008_ == 0 {
                                v___x_1001_ = v___x_998_;
                                v_isShared_1002_ = v_isSharedCheck_1008_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_999_);
                                leanh::lean_dec(v___x_998_);
                                v___x_1001_ = leanh::lean_box(0);
                                v_isShared_1002_ = v_isSharedCheck_1008_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1009_ = leanh::lean_ctor_get(v___x_998_, 0);
                            v_isSharedCheck_1045_ =
                                (!leanh::lean_is_exclusive(v___x_998_)) as u8;
                            if v_isSharedCheck_1045_ == 0 {
                                v___x_1011_ = v___x_998_;
                                v_isShared_1012_ = v_isSharedCheck_1045_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1009_);
                                leanh::lean_dec(v___x_998_);
                                v___x_1011_ = leanh::lean_box(0);
                                v_isShared_1012_ = v_isSharedCheck_1045_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_stx_979_);
                        v_a_1046_ = leanh::lean_ctor_get(v___x_994_, 0);
                        v_isSharedCheck_1053_ =
                            (!leanh::lean_is_exclusive(v___x_994_)) as u8;
                        if v_isSharedCheck_1053_ == 0 {
                            v___x_1048_ = v___x_994_;
                            v_isShared_1049_ = v_isSharedCheck_1053_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1046_);
                            leanh::lean_dec(v___x_994_);
                            v___x_1048_ = leanh::lean_box(0);
                            v_isShared_1049_ = v_isSharedCheck_1053_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1003_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1003_, 0, v_a_999_);
                v___x_1004_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1004_, 0, v___x_1003_);
                leanh::lean_ctor_set(v___x_1004_, 1, v___x_997_);
                if v_isShared_1002_ == 0 {
                    leanh::lean_ctor_set(v___x_1001_, 0, v___x_1004_);
                    v___x_1006_ = v___x_1001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
                    v___x_1006_ = v_reuseFailAlloc_1007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1006_;
            }
            3 => {
                v___x_1013_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0;
                v___x_1043_ = l_Lean_Exception_isInterrupt(v_a_1009_);
                if v___x_1043_ == 0 {
                    leanh::lean_inc(v_a_1009_);
                    v___x_1044_ = l_Lean_Exception_isRuntime(v_a_1009_);
                    v___y_1015_ = v___x_1044_;
                    state = 4;
                    continue;
                } else {
                    v___y_1015_ = v___x_1043_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_1015_ == 0 {
                    leanh::lean_del_object(v___x_1011_);
                    v___x_1016_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(
                        v_a_995_,
                        v___y_1015_,
                        v___y_983_,
                        v___y_984_,
                        v___y_985_,
                        v___y_986_,
                        v___y_987_,
                        v___y_988_,
                        v___y_989_,
                    );
                    if leanh::lean_obj_tag(v___x_1016_) == 0 {
                        v_isSharedCheck_1030_ =
                            (!leanh::lean_is_exclusive(v___x_1016_)) as u8;
                        if v_isSharedCheck_1030_ == 0 {
                            v_unused_1031_ = leanh::lean_ctor_get(v___x_1016_, 0);
                            leanh::lean_dec(v_unused_1031_);
                            v___x_1018_ = v___x_1016_;
                            v_isShared_1019_ = v_isSharedCheck_1030_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1016_);
                            v___x_1018_ = leanh::lean_box(0);
                            v_isShared_1019_ = v_isSharedCheck_1030_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1009_);
                        leanh::lean_dec(v_stx_979_);
                        v_a_1032_ = leanh::lean_ctor_get(v___x_1016_, 0);
                        v_isSharedCheck_1039_ =
                            (!leanh::lean_is_exclusive(v___x_1016_)) as u8;
                        if v_isSharedCheck_1039_ == 0 {
                            v___x_1034_ = v___x_1016_;
                            v_isShared_1035_ = v_isSharedCheck_1039_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1032_);
                            leanh::lean_dec(v___x_1016_);
                            v___x_1034_ = leanh::lean_box(0);
                            v_isShared_1035_ = v_isSharedCheck_1039_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_995_);
                    leanh::lean_dec(v_stx_979_);
                    if v_isShared_1012_ == 0 {
                        v___x_1041_ = v___x_1011_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1042_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1009_);
                        v___x_1041_ = v_reuseFailAlloc_1042_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_1009_) == 1 {
                    v_id_1020_ = leanh::lean_ctor_get(v_a_1009_, 0);
                    v___x_1021_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_1022_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1020_, v___x_1021_);
                    if v___x_1022_ == 0 {
                        leanh::lean_dec(v_stx_979_);
                        if v_isShared_1019_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1018_, 1);
                            leanh::lean_ctor_set(v___x_1018_, 0, v_a_1009_);
                            v___x_1024_ = v___x_1018_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1025_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1009_);
                            v___x_1024_ = v_reuseFailAlloc_1025_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_1009_, 2);
                        leanh::lean_del_object(v___x_1018_);
                        v_as_x27_980_ = v_tail_993_;
                        v_b_981_ = v___x_1013_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_stx_979_);
                    if v_isShared_1019_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1018_, 1);
                        leanh::lean_ctor_set(v___x_1018_, 0, v_a_1009_);
                        v___x_1028_ = v___x_1018_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1029_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1009_);
                        v___x_1028_ = v_reuseFailAlloc_1029_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1024_;
            }
            7 => {
                return v___x_1028_;
            }
            8 => {
                if v_isShared_1035_ == 0 {
                    v___x_1037_ = v___x_1034_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
                    v___x_1037_ = v_reuseFailAlloc_1038_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1037_;
            }
            10 => {
                return v___x_1041_;
            }
            11 => {
                if v_isShared_1049_ == 0 {
                    v___x_1051_ = v___x_1048_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1052_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
                    v___x_1051_ = v_reuseFailAlloc_1052_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___boxed(
    mut v_stx_1054_: *mut leanh::LeanObject,
    mut v_as_x27_1055_: *mut leanh::LeanObject,
    mut v_b_1056_: *mut leanh::LeanObject,
    mut v___y_1057_: *mut leanh::LeanObject,
    mut v___y_1058_: *mut leanh::LeanObject,
    mut v___y_1059_: *mut leanh::LeanObject,
    mut v___y_1060_: *mut leanh::LeanObject,
    mut v___y_1061_: *mut leanh::LeanObject,
    mut v___y_1062_: *mut leanh::LeanObject,
    mut v___y_1063_: *mut leanh::LeanObject,
    mut v___y_1064_: *mut leanh::LeanObject,
    mut v___y_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1066_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(
            v_stx_1054_,
            v_as_x27_1055_,
            v_b_1056_,
            v___y_1057_,
            v___y_1058_,
            v___y_1059_,
            v___y_1060_,
            v___y_1061_,
            v___y_1062_,
            v___y_1063_,
            v___y_1064_,
        );
    leanh::lean_dec(v___y_1064_);
    leanh::lean_dec_ref(v___y_1063_);
    leanh::lean_dec(v___y_1062_);
    leanh::lean_dec_ref(v___y_1061_);
    leanh::lean_dec(v___y_1060_);
    leanh::lean_dec_ref(v___y_1059_);
    leanh::lean_dec(v___y_1058_);
    leanh::lean_dec_ref(v___y_1057_);
    leanh::lean_dec(v_as_x27_1055_);
    return v_res_1066_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__0;
    v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
    return v___x_1069_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabSymDischarger(
    mut v_stx_1070_: *mut leanh::LeanObject,
    mut v_a_1071_: *mut leanh::LeanObject,
    mut v_a_1072_: *mut leanh::LeanObject,
    mut v_a_1073_: *mut leanh::LeanObject,
    mut v_a_1074_: *mut leanh::LeanObject,
    mut v_a_1075_: *mut leanh::LeanObject,
    mut v_a_1076_: *mut leanh::LeanObject,
    mut v_a_1077_: *mut leanh::LeanObject,
    mut v_a_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1090_: u8 = 0;
    let mut v_fst_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut v_unused_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v_a_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1080_ = lean_st_ref_get(v_a_1078_);
                v_env_1081_ = leanh::lean_ctor_get(v___x_1080_, 0);
                leanh::lean_inc_ref(v_env_1081_);
                leanh::lean_dec(v___x_1080_);
                v___x_1082_ = l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
                leanh::lean_inc_n(v_stx_1070_, 2);
                v___x_1083_ = l_Lean_Syntax_getKind(v_stx_1070_);
                v___x_1084_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(
                    v___x_1082_,
                    v_env_1081_,
                    v___x_1083_,
                );
                v___x_1085_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0;
                v___x_1086_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(v_stx_1070_, v___x_1084_, v___x_1085_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
                leanh::lean_dec(v___x_1084_);
                if leanh::lean_obj_tag(v___x_1086_) == 0 {
                    v_a_1087_ = leanh::lean_ctor_get(v___x_1086_, 0);
                    v_isSharedCheck_1109_ = (!leanh::lean_is_exclusive(v___x_1086_)) as u8;
                    if v_isSharedCheck_1109_ == 0 {
                        v___x_1089_ = v___x_1086_;
                        v_isShared_1090_ = v_isSharedCheck_1109_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1087_);
                        leanh::lean_dec(v___x_1086_);
                        v___x_1089_ = leanh::lean_box(0);
                        v_isShared_1090_ = v_isSharedCheck_1109_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1083_);
                    leanh::lean_dec(v_stx_1070_);
                    v_a_1110_ = leanh::lean_ctor_get(v___x_1086_, 0);
                    v_isSharedCheck_1117_ = (!leanh::lean_is_exclusive(v___x_1086_)) as u8;
                    if v_isSharedCheck_1117_ == 0 {
                        v___x_1112_ = v___x_1086_;
                        v_isShared_1113_ = v_isSharedCheck_1117_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1110_);
                        leanh::lean_dec(v___x_1086_);
                        v___x_1112_ = leanh::lean_box(0);
                        v_isShared_1113_ = v_isSharedCheck_1117_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1091_ = leanh::lean_ctor_get(v_a_1087_, 0);
                v_isSharedCheck_1107_ = (!leanh::lean_is_exclusive(v_a_1087_)) as u8;
                if v_isSharedCheck_1107_ == 0 {
                    v_unused_1108_ = leanh::lean_ctor_get(v_a_1087_, 1);
                    leanh::lean_dec(v_unused_1108_);
                    v___x_1093_ = v_a_1087_;
                    v_isShared_1094_ = v_isSharedCheck_1107_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_1091_);
                    leanh::lean_dec(v_a_1087_);
                    v___x_1093_ = leanh::lean_box(0);
                    v_isShared_1094_ = v_isSharedCheck_1107_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_1091_) == 0 {
                    leanh::lean_del_object(v___x_1089_);
                    v___x_1095_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1,
                    );
                    v___x_1096_ = l_Lean_MessageData_ofName(v___x_1083_);
                    if v_isShared_1094_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1093_, 7);
                        leanh::lean_ctor_set(v___x_1093_, 1, v___x_1096_);
                        leanh::lean_ctor_set(v___x_1093_, 0, v___x_1095_);
                        v___x_1098_ = v___x_1093_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1102_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1095_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1096_);
                        v___x_1098_ = v_reuseFailAlloc_1102_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1093_);
                    leanh::lean_dec(v___x_1083_);
                    leanh::lean_dec(v_stx_1070_);
                    v_val_1103_ = leanh::lean_ctor_get(v_fst_1091_, 0);
                    leanh::lean_inc(v_val_1103_);
                    leanh::lean_dec_ref_known(v_fst_1091_, 1);
                    if v_isShared_1090_ == 0 {
                        leanh::lean_ctor_set(v___x_1089_, 0, v_val_1103_);
                        v___x_1105_ = v___x_1089_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_val_1103_);
                        v___x_1105_ = v_reuseFailAlloc_1106_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1099_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3_once
                    ),
                    _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3,
                );
                v___x_1100_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1100_, 0, v___x_1098_);
                leanh::lean_ctor_set(v___x_1100_, 1, v___x_1099_);
                v___x_1101_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(v_stx_1070_, v___x_1100_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
                leanh::lean_dec(v_stx_1070_);
                return v___x_1101_;
            }
            4 => {
                return v___x_1105_;
            }
            5 => {
                if v_isShared_1113_ == 0 {
                    v___x_1115_ = v___x_1112_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1116_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
                    v___x_1115_ = v_reuseFailAlloc_1116_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabSymDischarger___boxed(
    mut v_stx_1118_: *mut leanh::LeanObject,
    mut v_a_1119_: *mut leanh::LeanObject,
    mut v_a_1120_: *mut leanh::LeanObject,
    mut v_a_1121_: *mut leanh::LeanObject,
    mut v_a_1122_: *mut leanh::LeanObject,
    mut v_a_1123_: *mut leanh::LeanObject,
    mut v_a_1124_: *mut leanh::LeanObject,
    mut v_a_1125_: *mut leanh::LeanObject,
    mut v_a_1126_: *mut leanh::LeanObject,
    mut v_a_1127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1128_ = l_Lean_Elab_Tactic_Grind_elabSymDischarger(
        v_stx_1118_,
        v_a_1119_,
        v_a_1120_,
        v_a_1121_,
        v_a_1122_,
        v_a_1123_,
        v_a_1124_,
        v_a_1125_,
        v_a_1126_,
    );
    leanh::lean_dec(v_a_1126_);
    leanh::lean_dec_ref(v_a_1125_);
    leanh::lean_dec(v_a_1124_);
    leanh::lean_dec_ref(v_a_1123_);
    leanh::lean_dec(v_a_1122_);
    leanh::lean_dec_ref(v_a_1121_);
    leanh::lean_dec(v_a_1120_);
    leanh::lean_dec_ref(v_a_1119_);
    return v_res_1128_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0(
    mut v_stx_1129_: *mut leanh::LeanObject,
    mut v_as_1130_: *mut leanh::LeanObject,
    mut v_as_x27_1131_: *mut leanh::LeanObject,
    mut v_b_1132_: *mut leanh::LeanObject,
    mut v_a_1133_: *mut leanh::LeanObject,
    mut v___y_1134_: *mut leanh::LeanObject,
    mut v___y_1135_: *mut leanh::LeanObject,
    mut v___y_1136_: *mut leanh::LeanObject,
    mut v___y_1137_: *mut leanh::LeanObject,
    mut v___y_1138_: *mut leanh::LeanObject,
    mut v___y_1139_: *mut leanh::LeanObject,
    mut v___y_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(
            v_stx_1129_,
            v_as_x27_1131_,
            v_b_1132_,
            v___y_1134_,
            v___y_1135_,
            v___y_1136_,
            v___y_1137_,
            v___y_1138_,
            v___y_1139_,
            v___y_1140_,
            v___y_1141_,
        );
    return v___x_1143_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___boxed(
    mut v_stx_1144_: *mut leanh::LeanObject,
    mut v_as_1145_: *mut leanh::LeanObject,
    mut v_as_x27_1146_: *mut leanh::LeanObject,
    mut v_b_1147_: *mut leanh::LeanObject,
    mut v_a_1148_: *mut leanh::LeanObject,
    mut v___y_1149_: *mut leanh::LeanObject,
    mut v___y_1150_: *mut leanh::LeanObject,
    mut v___y_1151_: *mut leanh::LeanObject,
    mut v___y_1152_: *mut leanh::LeanObject,
    mut v___y_1153_: *mut leanh::LeanObject,
    mut v___y_1154_: *mut leanh::LeanObject,
    mut v___y_1155_: *mut leanh::LeanObject,
    mut v___y_1156_: *mut leanh::LeanObject,
    mut v___y_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1158_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0(
        v_stx_1144_,
        v_as_1145_,
        v_as_x27_1146_,
        v_b_1147_,
        v_a_1148_,
        v___y_1149_,
        v___y_1150_,
        v___y_1151_,
        v___y_1152_,
        v___y_1153_,
        v___y_1154_,
        v___y_1155_,
        v___y_1156_,
    );
    leanh::lean_dec(v___y_1156_);
    leanh::lean_dec_ref(v___y_1155_);
    leanh::lean_dec(v___y_1154_);
    leanh::lean_dec_ref(v___y_1153_);
    leanh::lean_dec(v___y_1152_);
    leanh::lean_dec_ref(v___y_1151_);
    leanh::lean_dec(v___y_1150_);
    leanh::lean_dec_ref(v___y_1149_);
    leanh::lean_dec(v_as_x27_1146_);
    leanh::lean_dec(v_as_1145_);
    return v_res_1158_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(
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
    res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_SimprocDSL(
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
    res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Sym_Simp_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
}