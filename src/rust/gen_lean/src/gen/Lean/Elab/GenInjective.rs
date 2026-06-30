// Lean compiler output
// Module: Lean.Elab.GenInjective
// Imports: Lean.Elab.Command Lean.Meta.Injective Lean.Meta.Constructions.CtorIdx
use crate::r#gen::Init::Prelude::l_Lean_Syntax_getArg;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_liftTermElabM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_mkCtorIdx,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::Injective::{
    initialize_Lean_Meta_Injective, l_Lean_Meta_mkInjectiveTheorems,
    runtime_initialize_Lean_Meta_Injective,
};
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [103, 101, 110, 73, 110, 106, 101, 99, 116, 105, 118, 101, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__3_value) as *mut leanh::LeanObject,13979199899680194611 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__5_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [71, 101, 110, 73, 110, 106, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__10_value) as *mut leanh::LeanObject,1831590326038283434 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__11_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,15766973221561412779 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__12_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__0_value) as *mut leanh::LeanObject,8926060025602177174 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__8_value) as *mut leanh::LeanObject,2160535094612547780 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__14_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__2_value) as *mut leanh::LeanObject,310123643824003617 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 108, 97, 98, 71, 101, 110, 73, 110, 106, 101, 99, 116, 105, 118, 101, 84, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__15_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__16_value) as *mut leanh::LeanObject,9854580972373139301 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(
    mut v___x_94_: *mut leanh::LeanObject,
    mut v___x_95_: *mut leanh::LeanObject,
    mut v___y_96_: *mut leanh::LeanObject,
    mut v___y_97_: *mut leanh::LeanObject,
    mut v___y_98_: *mut leanh::LeanObject,
    mut v___y_99_: *mut leanh::LeanObject,
    mut v___y_100_: *mut leanh::LeanObject,
    mut v___y_101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_110_: u8 = 0;
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_103_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                    v___x_94_, v___x_95_, v___y_100_, v___y_101_,
                );
                if leanh::lean_obj_tag(v___x_103_) == 0 {
                    v_a_104_ = leanh::lean_ctor_get(v___x_103_, 0);
                    leanh::lean_inc_n(v_a_104_, 2);
                    leanh::lean_dec_ref_known(v___x_103_, 1);
                    v___x_105_ =
                        l_mkCtorIdx(v_a_104_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
                    if leanh::lean_obj_tag(v___x_105_) == 0 {
                        leanh::lean_dec_ref_known(v___x_105_, 1);
                        v___x_106_ = l_Lean_Meta_mkInjectiveTheorems(
                            v_a_104_, v___y_98_, v___y_99_, v___y_100_, v___y_101_,
                        );
                        return v___x_106_;
                    } else {
                        leanh::lean_dec(v_a_104_);
                        return v___x_105_;
                    }
                } else {
                    v_a_107_ = leanh::lean_ctor_get(v___x_103_, 0);
                    v_isSharedCheck_114_ = (!leanh::lean_is_exclusive(v___x_103_)) as u8;
                    if v_isSharedCheck_114_ == 0 {
                        v___x_109_ = v___x_103_;
                        v_isShared_110_ = v_isSharedCheck_114_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_107_);
                        leanh::lean_dec(v___x_103_);
                        v___x_109_ = leanh::lean_box(0);
                        v_isShared_110_ = v_isSharedCheck_114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_110_ == 0 {
                    v___x_112_ = v___x_109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_113_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
                    v___x_112_ = v_reuseFailAlloc_113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed(
    mut v___x_115_: *mut leanh::LeanObject,
    mut v___x_116_: *mut leanh::LeanObject,
    mut v___y_117_: *mut leanh::LeanObject,
    mut v___y_118_: *mut leanh::LeanObject,
    mut v___y_119_: *mut leanh::LeanObject,
    mut v___y_120_: *mut leanh::LeanObject,
    mut v___y_121_: *mut leanh::LeanObject,
    mut v___y_122_: *mut leanh::LeanObject,
    mut v___y_123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_124_ =
        l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0(
            v___x_115_, v___x_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_,
            v___y_122_,
        );
    leanh::lean_dec(v___y_122_);
    leanh::lean_dec_ref(v___y_121_);
    leanh::lean_dec(v___y_120_);
    leanh::lean_dec_ref(v___y_119_);
    leanh::lean_dec(v___y_118_);
    leanh::lean_dec_ref(v___y_117_);
    return v_res_124_;
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(
    mut v_stx_125_: *mut leanh::LeanObject,
    mut v_a_126_: *mut leanh::LeanObject,
    mut v_a_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_129_ = leanh::lean_unsigned_to_nat(1);
    v___x_130_ = l_Lean_Syntax_getArg(v_stx_125_, v___x_129_);
    v___x_131_ = leanh::lean_box(0);
    v___f_132_ = leanh::lean_alloc_closure(l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
    leanh::lean_closure_set(v___f_132_, 0, v___x_130_);
    leanh::lean_closure_set(v___f_132_, 1, v___x_131_);
    v___x_133_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_132_, v_a_126_, v_a_127_);
    return v___x_133_;
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed(
    mut v_stx_134_: *mut leanh::LeanObject,
    mut v_a_135_: *mut leanh::LeanObject,
    mut v_a_136_: *mut leanh::LeanObject,
    mut v_a_137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_138_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems(
        v_stx_134_, v_a_135_, v_a_136_,
    );
    leanh::lean_dec(v_a_136_);
    leanh::lean_dec_ref(v_a_135_);
    leanh::lean_dec(v_stx_134_);
    return v_res_138_;
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1()
-> *mut leanh::LeanObject {
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_180_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_181_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__4;
    v___x_182_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___closed__17;
    v___x_183_ = leanh::lean_alloc_closure(
        l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___boxed
            as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_184_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_180_, v___x_181_, v___x_182_, v___x_183_,
    );
    return v___x_184_;
}
pub unsafe fn l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1___boxed(
    mut v_a_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_186_ = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
    return v_res_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_GenInjective(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Injective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems___regBuiltin___private_Lean_Elab_GenInjective_0__Lean_Elab_Command_elabGenInjectiveTheorems__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_GenInjective(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_GenInjective(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Injective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_GenInjective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_GenInjective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_GenInjective(builtin);
}