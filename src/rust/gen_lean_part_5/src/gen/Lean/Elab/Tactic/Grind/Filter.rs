// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Filter
// Imports: Lean.Elab.Tactic.Grind.Basic Lean.Meta.Tactic.Grind.Filter
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get};
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getNat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Grind::Basic::{
    initialize_Lean_Elab_Tactic_Grind_Basic, runtime_initialize_Lean_Elab_Tactic_Grind_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_resolveId_x3f;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Tactic::Grind::Filter::{
    initialize_Lean_Meta_Tactic_Grind_Filter, runtime_initialize_Lean_Meta_Tactic_Grind_Filter,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__4_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__4_value) as *mut leanh::LeanObject,17749774379613861674 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__6_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 95, 38, 38, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__6_value) as *mut leanh::LeanObject,2546887458887176769 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__8_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 95, 124, 124, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__8_value) as *mut leanh::LeanObject,13925358296987369388 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__10_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 33, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__10_value) as *mut leanh::LeanObject,1993779534650405055 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__12_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 40, 95, 41, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__12_value) as *mut leanh::LeanObject,1261507149438490230 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__14_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 61, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__14_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__14_value) as *mut leanh::LeanObject,10897721082736832046 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__16_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 62, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__16_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__16_value) as *mut leanh::LeanObject,4600612048943183243 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__18_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 17, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 226, 137, 165, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__18_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__18_value) as *mut leanh::LeanObject,2486500500062112323 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__20_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 62, 61, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__20_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__20_value) as *mut leanh::LeanObject,4587601961659498949 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__22_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 17, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 226, 137, 164, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__22_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__22_value) as *mut leanh::LeanObject,13823788008300330912 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__24_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 60, 61, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__24_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__24_value) as *mut leanh::LeanObject,13433549983839248510 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__26_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 60, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__26_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__26_value) as *mut leanh::LeanObject,14191831149334518614 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__28_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [103, 114, 105, 110, 100, 95, 102, 105, 108, 116, 101, 114, 71, 101, 110, 33, 61, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__28_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__3_value) as *mut leanh::LeanObject,3168557723425139092 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__28_value) as *mut leanh::LeanObject,12297617841168749882 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__30_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__30_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__30_value) as *mut leanh::LeanObject,6110315075117401315 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__32_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = leanh::lean_box(0);
    v___x_568_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_569_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_569_, 0, v___x_568_);
    leanh::lean_ctor_set(v___x_569_, 1, v___x_567_);
    return v___x_569_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___closed__0);
    v___x_572_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_572_, 0, v___x_571_);
    return v___x_572_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg___boxed(
    mut v___y_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
    return v_res_574_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(
    mut v_00_u03b1_575_: *mut leanh::LeanObject,
    mut v___y_576_: *mut leanh::LeanObject,
    mut v___y_577_: *mut leanh::LeanObject,
    mut v___y_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
    mut v___y_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_585_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
    return v___x_585_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___boxed(
    mut v_00_u03b1_586_: *mut leanh::LeanObject,
    mut v___y_587_: *mut leanh::LeanObject,
    mut v___y_588_: *mut leanh::LeanObject,
    mut v___y_589_: *mut leanh::LeanObject,
    mut v___y_590_: *mut leanh::LeanObject,
    mut v___y_591_: *mut leanh::LeanObject,
    mut v___y_592_: *mut leanh::LeanObject,
    mut v___y_593_: *mut leanh::LeanObject,
    mut v___y_594_: *mut leanh::LeanObject,
    mut v___y_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0(v_00_u03b1_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
    leanh::lean_dec(v___y_594_);
    leanh::lean_dec_ref(v___y_593_);
    leanh::lean_dec(v___y_592_);
    leanh::lean_dec_ref(v___y_591_);
    leanh::lean_dec(v___y_590_);
    leanh::lean_dec_ref(v___y_589_);
    leanh::lean_dec(v___y_588_);
    leanh::lean_dec_ref(v___y_587_);
    return v_res_596_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(
    mut v_n_597_: *mut leanh::LeanObject,
    mut v___x_598_: u8,
    mut v___x_599_: u8,
    mut v_x_600_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_601_: u8 = 0;
    v___x_601_ = lean_nat_dec_eq(v_x_600_, v_n_597_);
    if v___x_601_ == 0 {
        return v___x_598_;
    } else {
        return v___x_599_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed(
    mut v_n_602_: *mut leanh::LeanObject,
    mut v___x_603_: *mut leanh::LeanObject,
    mut v___x_604_: *mut leanh::LeanObject,
    mut v_x_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_19736__boxed_606_: u8 = 0;
    let mut v___x_19737__boxed_607_: u8 = 0;
    let mut v_res_608_: u8 = 0;
    let mut v_r_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_19736__boxed_606_ = (leanh::lean_unbox(v___x_603_) as u8);
    v___x_19737__boxed_607_ = (leanh::lean_unbox(v___x_604_) as u8);
    v_res_608_ =
        l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0(
            v_n_602_,
            v___x_19736__boxed_606_,
            v___x_19737__boxed_607_,
            v_x_605_,
        );
    leanh::lean_dec(v_x_605_);
    leanh::lean_dec(v_n_602_);
    v_r_609_ = leanh::lean_box((v_res_608_) as usize);
    return v_r_609_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(
    mut v_n_610_: *mut leanh::LeanObject,
    mut v_x_611_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_612_: u8 = 0;
    v___x_612_ = lean_nat_dec_lt(v_x_611_, v_n_610_);
    return v___x_612_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed(
    mut v_n_613_: *mut leanh::LeanObject,
    mut v_x_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_615_: u8 = 0;
    let mut v_r_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_615_ =
        l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1(
            v_n_613_, v_x_614_,
        );
    leanh::lean_dec(v_x_614_);
    leanh::lean_dec(v_n_613_);
    v_r_616_ = leanh::lean_box((v_res_615_) as usize);
    return v_r_616_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(
    mut v_n_617_: *mut leanh::LeanObject,
    mut v_x_618_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_619_: u8 = 0;
    v___x_619_ = lean_nat_dec_le(v_x_618_, v_n_617_);
    return v___x_619_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed(
    mut v_n_620_: *mut leanh::LeanObject,
    mut v_x_621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_622_: u8 = 0;
    let mut v_r_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_622_ =
        l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2(
            v_n_620_, v_x_621_,
        );
    leanh::lean_dec(v_x_621_);
    leanh::lean_dec(v_n_620_);
    v_r_623_ = leanh::lean_box((v_res_622_) as usize);
    return v_r_623_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(
    mut v_n_624_: *mut leanh::LeanObject,
    mut v_x_625_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_626_: u8 = 0;
    v___x_626_ = lean_nat_dec_le(v_n_624_, v_x_625_);
    return v___x_626_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed(
    mut v_n_627_: *mut leanh::LeanObject,
    mut v_x_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_629_: u8 = 0;
    let mut v_r_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ =
        l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4(
            v_n_627_, v_x_628_,
        );
    leanh::lean_dec(v_x_628_);
    leanh::lean_dec(v_n_627_);
    v_r_630_ = leanh::lean_box((v_res_629_) as usize);
    return v_r_630_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(
    mut v_n_631_: *mut leanh::LeanObject,
    mut v_x_632_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_633_: u8 = 0;
    v___x_633_ = lean_nat_dec_lt(v_n_631_, v_x_632_);
    return v___x_633_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed(
    mut v_n_634_: *mut leanh::LeanObject,
    mut v_x_635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_636_: u8 = 0;
    let mut v_r_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_636_ =
        l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5(
            v_n_634_, v_x_635_,
        );
    leanh::lean_dec(v_x_635_);
    leanh::lean_dec(v_n_634_);
    v_r_637_ = leanh::lean_box((v_res_636_) as usize);
    return v_r_637_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(
    mut v_n_638_: *mut leanh::LeanObject,
    mut v_x_639_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_640_: u8 = 0;
    v___x_640_ = lean_nat_dec_eq(v_x_639_, v_n_638_);
    return v___x_640_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed(
    mut v_n_641_: *mut leanh::LeanObject,
    mut v_x_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_643_: u8 = 0;
    let mut v_r_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ =
        l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3(
            v_n_641_, v_x_642_,
        );
    leanh::lean_dec(v_x_642_);
    leanh::lean_dec(v_n_641_);
    v_r_644_ = leanh::lean_box((v_res_643_) as usize);
    return v_r_644_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(
    mut v_msgData_645_: *mut leanh::LeanObject,
    mut v___y_646_: *mut leanh::LeanObject,
    mut v___y_647_: *mut leanh::LeanObject,
    mut v___y_648_: *mut leanh::LeanObject,
    mut v___y_649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_651_ = lean_st_ref_get(v___y_649_);
    v_env_652_ = leanh::lean_ctor_get(v___x_651_, 0);
    leanh::lean_inc_ref(v_env_652_);
    leanh::lean_dec(v___x_651_);
    v___x_653_ = lean_st_ref_get(v___y_647_);
    v_mctx_654_ = leanh::lean_ctor_get(v___x_653_, 0);
    leanh::lean_inc_ref(v_mctx_654_);
    leanh::lean_dec(v___x_653_);
    v_lctx_655_ = leanh::lean_ctor_get(v___y_646_, 2);
    v_options_656_ = leanh::lean_ctor_get(v___y_648_, 2);
    leanh::lean_inc_ref(v_options_656_);
    leanh::lean_inc_ref(v_lctx_655_);
    v___x_657_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_657_, 0, v_env_652_);
    leanh::lean_ctor_set(v___x_657_, 1, v_mctx_654_);
    leanh::lean_ctor_set(v___x_657_, 2, v_lctx_655_);
    leanh::lean_ctor_set(v___x_657_, 3, v_options_656_);
    v___x_658_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_658_, 0, v___x_657_);
    leanh::lean_ctor_set(v___x_658_, 1, v_msgData_645_);
    v___x_659_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_659_, 0, v___x_658_);
    return v___x_659_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_660_: *mut leanh::LeanObject,
    mut v___y_661_: *mut leanh::LeanObject,
    mut v___y_662_: *mut leanh::LeanObject,
    mut v___y_663_: *mut leanh::LeanObject,
    mut v___y_664_: *mut leanh::LeanObject,
    mut v___y_665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msgData_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
    leanh::lean_dec(v___y_664_);
    leanh::lean_dec_ref(v___y_663_);
    leanh::lean_dec(v___y_662_);
    leanh::lean_dec_ref(v___y_661_);
    return v_res_666_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(
    mut v_msg_667_: *mut leanh::LeanObject,
    mut v___y_668_: *mut leanh::LeanObject,
    mut v___y_669_: *mut leanh::LeanObject,
    mut v___y_670_: *mut leanh::LeanObject,
    mut v___y_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_673_ = leanh::lean_ctor_get(v___y_670_, 5);
                v___x_674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1_spec__2(v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
                v_a_675_ = leanh::lean_ctor_get(v___x_674_, 0);
                v_isSharedCheck_683_ = (!leanh::lean_is_exclusive(v___x_674_)) as u8;
                if v_isSharedCheck_683_ == 0 {
                    v___x_677_ = v___x_674_;
                    v_isShared_678_ = v_isSharedCheck_683_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_675_);
                    leanh::lean_dec(v___x_674_);
                    v___x_677_ = leanh::lean_box(0);
                    v_isShared_678_ = v_isSharedCheck_683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_673_);
                v___x_679_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_679_, 0, v_ref_673_);
                leanh::lean_ctor_set(v___x_679_, 1, v_a_675_);
                if v_isShared_678_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_677_, 1);
                    leanh::lean_ctor_set(v___x_677_, 0, v___x_679_);
                    v___x_681_ = v___x_677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
                    v___x_681_ = v_reuseFailAlloc_682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg___boxed(
    mut v_msg_684_: *mut leanh::LeanObject,
    mut v___y_685_: *mut leanh::LeanObject,
    mut v___y_686_: *mut leanh::LeanObject,
    mut v___y_687_: *mut leanh::LeanObject,
    mut v___y_688_: *mut leanh::LeanObject,
    mut v___y_689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_690_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
    leanh::lean_dec(v___y_688_);
    leanh::lean_dec_ref(v___y_687_);
    leanh::lean_dec(v___y_686_);
    leanh::lean_dec_ref(v___y_685_);
    return v_res_690_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(
    mut v_ref_691_: *mut leanh::LeanObject,
    mut v_msg_692_: *mut leanh::LeanObject,
    mut v___y_693_: *mut leanh::LeanObject,
    mut v___y_694_: *mut leanh::LeanObject,
    mut v___y_695_: *mut leanh::LeanObject,
    mut v___y_696_: *mut leanh::LeanObject,
    mut v___y_697_: *mut leanh::LeanObject,
    mut v___y_698_: *mut leanh::LeanObject,
    mut v___y_699_: *mut leanh::LeanObject,
    mut v___y_700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_714_: u8 = 0;
    let mut v_cancelTk_x3f_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_716_: u8 = 0;
    let mut v_inheritedTraceOptions_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_702_ = leanh::lean_ctor_get(v___y_699_, 0);
    v_fileMap_703_ = leanh::lean_ctor_get(v___y_699_, 1);
    v_options_704_ = leanh::lean_ctor_get(v___y_699_, 2);
    v_currRecDepth_705_ = leanh::lean_ctor_get(v___y_699_, 3);
    v_maxRecDepth_706_ = leanh::lean_ctor_get(v___y_699_, 4);
    v_ref_707_ = leanh::lean_ctor_get(v___y_699_, 5);
    v_currNamespace_708_ = leanh::lean_ctor_get(v___y_699_, 6);
    v_openDecls_709_ = leanh::lean_ctor_get(v___y_699_, 7);
    v_initHeartbeats_710_ = leanh::lean_ctor_get(v___y_699_, 8);
    v_maxHeartbeats_711_ = leanh::lean_ctor_get(v___y_699_, 9);
    v_quotContext_712_ = leanh::lean_ctor_get(v___y_699_, 10);
    v_currMacroScope_713_ = leanh::lean_ctor_get(v___y_699_, 11);
    v_diag_714_ = leanh::lean_ctor_get_uint8(
        v___y_699_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_715_ = leanh::lean_ctor_get(v___y_699_, 12);
    v_suppressElabErrors_716_ = leanh::lean_ctor_get_uint8(
        v___y_699_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_717_ = leanh::lean_ctor_get(v___y_699_, 13);
    v_ref_718_ = l_Lean_replaceRef(v_ref_691_, v_ref_707_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_717_);
    leanh::lean_inc(v_cancelTk_x3f_715_);
    leanh::lean_inc(v_currMacroScope_713_);
    leanh::lean_inc(v_quotContext_712_);
    leanh::lean_inc(v_maxHeartbeats_711_);
    leanh::lean_inc(v_initHeartbeats_710_);
    leanh::lean_inc(v_openDecls_709_);
    leanh::lean_inc(v_currNamespace_708_);
    leanh::lean_inc(v_maxRecDepth_706_);
    leanh::lean_inc(v_currRecDepth_705_);
    leanh::lean_inc_ref(v_options_704_);
    leanh::lean_inc_ref(v_fileMap_703_);
    leanh::lean_inc_ref(v_fileName_702_);
    v___x_719_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_719_, 0, v_fileName_702_);
    leanh::lean_ctor_set(v___x_719_, 1, v_fileMap_703_);
    leanh::lean_ctor_set(v___x_719_, 2, v_options_704_);
    leanh::lean_ctor_set(v___x_719_, 3, v_currRecDepth_705_);
    leanh::lean_ctor_set(v___x_719_, 4, v_maxRecDepth_706_);
    leanh::lean_ctor_set(v___x_719_, 5, v_ref_718_);
    leanh::lean_ctor_set(v___x_719_, 6, v_currNamespace_708_);
    leanh::lean_ctor_set(v___x_719_, 7, v_openDecls_709_);
    leanh::lean_ctor_set(v___x_719_, 8, v_initHeartbeats_710_);
    leanh::lean_ctor_set(v___x_719_, 9, v_maxHeartbeats_711_);
    leanh::lean_ctor_set(v___x_719_, 10, v_quotContext_712_);
    leanh::lean_ctor_set(v___x_719_, 11, v_currMacroScope_713_);
    leanh::lean_ctor_set(v___x_719_, 12, v_cancelTk_x3f_715_);
    leanh::lean_ctor_set(v___x_719_, 13, v_inheritedTraceOptions_717_);
    leanh::lean_ctor_set_uint8(
        v___x_719_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_714_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_719_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_716_,
    );
    v___x_720_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_692_, v___y_697_, v___y_698_, v___x_719_, v___y_700_);
    leanh::lean_dec_ref_known(v___x_719_, 14);
    return v___x_720_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg___boxed(
    mut v_ref_721_: *mut leanh::LeanObject,
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
    v_res_732_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_721_, v_msg_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
    leanh::lean_dec(v___y_730_);
    leanh::lean_dec_ref(v___y_729_);
    leanh::lean_dec(v___y_728_);
    leanh::lean_dec_ref(v___y_727_);
    leanh::lean_dec(v___y_726_);
    leanh::lean_dec_ref(v___y_725_);
    leanh::lean_dec(v___y_724_);
    leanh::lean_dec_ref(v___y_723_);
    leanh::lean_dec(v_ref_721_);
    return v_res_732_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__35;
    v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
    return v___x_837_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(
    mut v_filter_838_: *mut leanh::LeanObject,
    mut v_a_839_: *mut leanh::LeanObject,
    mut v_a_840_: *mut leanh::LeanObject,
    mut v_a_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
    mut v_a_844_: *mut leanh::LeanObject,
    mut v_a_845_: *mut leanh::LeanObject,
    mut v_a_846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u8 = 0;
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u8 = 0;
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: u8 = 0;
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: u8 = 0;
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: u8 = 0;
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: u8 = 0;
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: u8 = 0;
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: u8 = 0;
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: u8 = 0;
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: u8 = 0;
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: u8 = 0;
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_958_: u8 = 0;
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_963_: u8 = 0;
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_974_: u8 = 0;
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u8 = 0;
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1007_: u8 = 0;
    let mut v___y_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1022_: u8 = 0;
    let mut v_declName_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1037_: u8 = 0;
    let mut v_isSharedCheck_1038_: u8 = 0;
    let mut v_a_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1042_: u8 = 0;
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_848_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__5;
                leanh::lean_inc(v_filter_838_);
                v___x_849_ = l_Lean_Syntax_isOfKind(v_filter_838_, v___x_848_);
                if v___x_849_ == 0 {
                    v___x_850_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__7;
                    leanh::lean_inc(v_filter_838_);
                    v___x_851_ = l_Lean_Syntax_isOfKind(v_filter_838_, v___x_850_);
                    if v___x_851_ == 0 {
                        v___x_852_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__9;
                        leanh::lean_inc(v_filter_838_);
                        v___x_853_ = l_Lean_Syntax_isOfKind(v_filter_838_, v___x_852_);
                        if v___x_853_ == 0 {
                            v___x_854_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__11;
                            leanh::lean_inc(v_filter_838_);
                            v___x_855_ = l_Lean_Syntax_isOfKind(v_filter_838_, v___x_854_);
                            if v___x_855_ == 0 {
                                v___x_856_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__13;
                                leanh::lean_inc(v_filter_838_);
                                v___x_857_ = l_Lean_Syntax_isOfKind(v_filter_838_, v___x_856_);
                                if v___x_857_ == 0 {
                                    v___x_858_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__15;
                                    leanh::lean_inc(v_filter_838_);
                                    v___x_859_ = l_Lean_Syntax_isOfKind(v_filter_838_, v___x_858_);
                                    if v___x_859_ == 0 {
                                        v___x_860_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__17;
                                        leanh::lean_inc(v_filter_838_);
                                        v___x_861_ =
                                            l_Lean_Syntax_isOfKind(v_filter_838_, v___x_860_);
                                        if v___x_861_ == 0 {
                                            v___x_862_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__19;
                                            leanh::lean_inc(v_filter_838_);
                                            v___x_863_ =
                                                l_Lean_Syntax_isOfKind(v_filter_838_, v___x_862_);
                                            if v___x_863_ == 0 {
                                                v___x_864_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__21;
                                                leanh::lean_inc(v_filter_838_);
                                                v___x_865_ = l_Lean_Syntax_isOfKind(
                                                    v_filter_838_,
                                                    v___x_864_,
                                                );
                                                if v___x_865_ == 0 {
                                                    v___x_866_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__23;
                                                    leanh::lean_inc(v_filter_838_);
                                                    v___x_867_ = l_Lean_Syntax_isOfKind(
                                                        v_filter_838_,
                                                        v___x_866_,
                                                    );
                                                    if v___x_867_ == 0 {
                                                        v___x_868_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__25;
                                                        leanh::lean_inc(v_filter_838_);
                                                        v___x_869_ = l_Lean_Syntax_isOfKind(
                                                            v_filter_838_,
                                                            v___x_868_,
                                                        );
                                                        if v___x_869_ == 0 {
                                                            v___x_870_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__27;
                                                            leanh::lean_inc(v_filter_838_);
                                                            v___x_871_ = l_Lean_Syntax_isOfKind(
                                                                v_filter_838_,
                                                                v___x_870_,
                                                            );
                                                            if v___x_871_ == 0 {
                                                                v___x_872_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__29;
                                                                leanh::lean_inc(
                                                                    v_filter_838_,
                                                                );
                                                                v___x_873_ = l_Lean_Syntax_isOfKind(
                                                                    v_filter_838_,
                                                                    v___x_872_,
                                                                );
                                                                if v___x_873_ == 0 {
                                                                    leanh::lean_dec(
                                                                        v_filter_838_,
                                                                    );
                                                                    v___x_874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                                                    return v___x_874_;
                                                                } else {
                                                                    v___x_875_ = leanh::lean_unsigned_to_nat(2);
                                                                    v_n_876_ = l_Lean_Syntax_getArg(
                                                                        v_filter_838_,
                                                                        v___x_875_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_filter_838_,
                                                                    );
                                                                    v___x_877_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31;
                                                                    leanh::lean_inc(
                                                                        v_n_876_,
                                                                    );
                                                                    v___x_878_ =
                                                                        l_Lean_Syntax_isOfKind(
                                                                            v_n_876_, v___x_877_,
                                                                        );
                                                                    if v___x_878_ == 0 {
                                                                        leanh::lean_dec(
                                                                            v_n_876_,
                                                                        );
                                                                        v___x_879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                                                        return v___x_879_;
                                                                    } else {
                                                                        v_n_880_ =
                                                                            l_Lean_TSyntax_getNat(
                                                                                v_n_876_,
                                                                            );
                                                                        leanh::lean_dec(
                                                                            v_n_876_,
                                                                        );
                                                                        v___x_881_ =
                                                                            leanh::lean_box(
                                                                                (v___x_878_)
                                                                                    as usize,
                                                                            );
                                                                        v___x_882_ =
                                                                            leanh::lean_box(
                                                                                (v___x_871_)
                                                                                    as usize,
                                                                            );
                                                                        v___f_883_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
                                                                        leanh::lean_closure_set(v___f_883_, 0, v_n_880_);
                                                                        leanh::lean_closure_set(v___f_883_, 1, v___x_881_);
                                                                        leanh::lean_closure_set(v___f_883_, 2, v___x_882_);
                                                                        v___x_884_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_884_, 0,
                                                                            v___f_883_,
                                                                        );
                                                                        v___x_885_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_885_, 0,
                                                                            v___x_884_,
                                                                        );
                                                                        return v___x_885_;
                                                                    }
                                                                }
                                                            } else {
                                                                v___x_886_ = leanh::lean_unsigned_to_nat(2);
                                                                v_n_887_ = l_Lean_Syntax_getArg(
                                                                    v_filter_838_,
                                                                    v___x_886_,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_filter_838_,
                                                                );
                                                                v___x_888_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31;
                                                                leanh::lean_inc(v_n_887_);
                                                                v___x_889_ = l_Lean_Syntax_isOfKind(
                                                                    v_n_887_, v___x_888_,
                                                                );
                                                                if v___x_889_ == 0 {
                                                                    leanh::lean_dec(
                                                                        v_n_887_,
                                                                    );
                                                                    v___x_890_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                                                    return v___x_890_;
                                                                } else {
                                                                    v_n_891_ =
                                                                        l_Lean_TSyntax_getNat(
                                                                            v_n_887_,
                                                                        );
                                                                    leanh::lean_dec(
                                                                        v_n_887_,
                                                                    );
                                                                    v___f_892_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                                                                    leanh::lean_closure_set(
                                                                        v___f_892_, 0, v_n_891_,
                                                                    );
                                                                    v___x_893_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_893_, 0, v___f_892_,
                                                                    );
                                                                    v___x_894_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_894_, 0, v___x_893_,
                                                                    );
                                                                    return v___x_894_;
                                                                }
                                                            }
                                                        } else {
                                                            v___x_895_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    2,
                                                                );
                                                            v_n_896_ = l_Lean_Syntax_getArg(
                                                                v_filter_838_,
                                                                v___x_895_,
                                                            );
                                                            leanh::lean_dec(v_filter_838_);
                                                            v___x_897_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31;
                                                            leanh::lean_inc(v_n_896_);
                                                            v___x_898_ = l_Lean_Syntax_isOfKind(
                                                                v_n_896_, v___x_897_,
                                                            );
                                                            if v___x_898_ == 0 {
                                                                leanh::lean_dec(v_n_896_);
                                                                v___x_899_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                                                return v___x_899_;
                                                            } else {
                                                                v_n_900_ =
                                                                    l_Lean_TSyntax_getNat(v_n_896_);
                                                                leanh::lean_dec(v_n_896_);
                                                                v___f_901_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed as *mut core::ffi::c_void, 2, 1);
                                                                leanh::lean_closure_set(
                                                                    v___f_901_, 0, v_n_900_,
                                                                );
                                                                v___x_902_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        3,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_902_, 0, v___f_901_,
                                                                );
                                                                v___x_903_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_903_, 0, v___x_902_,
                                                                );
                                                                return v___x_903_;
                                                            }
                                                        }
                                                    } else {
                                                        v___x_904_ =
                                                            leanh::lean_unsigned_to_nat(2);
                                                        v_n_905_ = l_Lean_Syntax_getArg(
                                                            v_filter_838_,
                                                            v___x_904_,
                                                        );
                                                        leanh::lean_dec(v_filter_838_);
                                                        v___x_906_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31;
                                                        leanh::lean_inc(v_n_905_);
                                                        v___x_907_ = l_Lean_Syntax_isOfKind(
                                                            v_n_905_, v___x_906_,
                                                        );
                                                        if v___x_907_ == 0 {
                                                            leanh::lean_dec(v_n_905_);
                                                            v___x_908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                                            return v___x_908_;
                                                        } else {
                                                            v_n_909_ =
                                                                l_Lean_TSyntax_getNat(v_n_905_);
                                                            leanh::lean_dec(v_n_905_);
                                                            v___f_910_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__2___boxed as *mut core::ffi::c_void, 2, 1);
                                                            leanh::lean_closure_set(
                                                                v___f_910_, 0, v_n_909_,
                                                            );
                                                            v___x_911_ =
                                                                leanh::lean_alloc_ctor(
                                                                    3,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_911_, 0, v___f_910_,
                                                            );
                                                            v___x_912_ =
                                                                leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_912_, 0, v___x_911_,
                                                            );
                                                            return v___x_912_;
                                                        }
                                                    }
                                                } else {
                                                    v___x_913_ =
                                                        leanh::lean_unsigned_to_nat(2);
                                                    v_n_914_ = l_Lean_Syntax_getArg(
                                                        v_filter_838_,
                                                        v___x_913_,
                                                    );
                                                    leanh::lean_dec(v_filter_838_);
                                                    v___x_915_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31;
                                                    leanh::lean_inc(v_n_914_);
                                                    v___x_916_ = l_Lean_Syntax_isOfKind(
                                                        v_n_914_, v___x_915_,
                                                    );
                                                    if v___x_916_ == 0 {
                                                        leanh::lean_dec(v_n_914_);
                                                        v___x_917_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                                        return v___x_917_;
                                                    } else {
                                                        v_n_918_ = l_Lean_TSyntax_getNat(v_n_914_);
                                                        leanh::lean_dec(v_n_914_);
                                                        v___f_919_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed as *mut core::ffi::c_void, 2, 1);
                                                        leanh::lean_closure_set(
                                                            v___f_919_, 0, v_n_918_,
                                                        );
                                                        v___x_920_ = leanh::lean_alloc_ctor(
                                                            3,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_920_, 0, v___f_919_,
                                                        );
                                                        v___x_921_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_921_, 0, v___x_920_,
                                                        );
                                                        return v___x_921_;
                                                    }
                                                }
                                            } else {
                                                v___x_922_ = leanh::lean_unsigned_to_nat(2);
                                                v_n_923_ =
                                                    l_Lean_Syntax_getArg(v_filter_838_, v___x_922_);
                                                leanh::lean_dec(v_filter_838_);
                                                v___x_924_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31;
                                                leanh::lean_inc(v_n_923_);
                                                v___x_925_ =
                                                    l_Lean_Syntax_isOfKind(v_n_923_, v___x_924_);
                                                if v___x_925_ == 0 {
                                                    leanh::lean_dec(v_n_923_);
                                                    v___x_926_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                                    return v___x_926_;
                                                } else {
                                                    v_n_927_ = l_Lean_TSyntax_getNat(v_n_923_);
                                                    leanh::lean_dec(v_n_923_);
                                                    v___f_928_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__4___boxed as *mut core::ffi::c_void, 2, 1);
                                                    leanh::lean_closure_set(
                                                        v___f_928_, 0, v_n_927_,
                                                    );
                                                    v___x_929_ = leanh::lean_alloc_ctor(
                                                        3,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_929_, 0, v___f_928_,
                                                    );
                                                    v___x_930_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_930_, 0, v___x_929_,
                                                    );
                                                    return v___x_930_;
                                                }
                                            }
                                        } else {
                                            v___x_931_ = leanh::lean_unsigned_to_nat(2);
                                            v_n_932_ =
                                                l_Lean_Syntax_getArg(v_filter_838_, v___x_931_);
                                            leanh::lean_dec(v_filter_838_);
                                            v___x_933_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31;
                                            leanh::lean_inc(v_n_932_);
                                            v___x_934_ =
                                                l_Lean_Syntax_isOfKind(v_n_932_, v___x_933_);
                                            if v___x_934_ == 0 {
                                                leanh::lean_dec(v_n_932_);
                                                v___x_935_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                                return v___x_935_;
                                            } else {
                                                v_n_936_ = l_Lean_TSyntax_getNat(v_n_932_);
                                                leanh::lean_dec(v_n_932_);
                                                v___f_937_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__5___boxed as *mut core::ffi::c_void, 2, 1);
                                                leanh::lean_closure_set(
                                                    v___f_937_, 0, v_n_936_,
                                                );
                                                v___x_938_ =
                                                    leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_938_, 0, v___f_937_,
                                                );
                                                v___x_939_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_939_, 0, v___x_938_,
                                                );
                                                return v___x_939_;
                                            }
                                        }
                                    } else {
                                        v___x_940_ = leanh::lean_unsigned_to_nat(2);
                                        v_n_941_ = l_Lean_Syntax_getArg(v_filter_838_, v___x_940_);
                                        leanh::lean_dec(v_filter_838_);
                                        v___x_942_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__31;
                                        leanh::lean_inc(v_n_941_);
                                        v___x_943_ = l_Lean_Syntax_isOfKind(v_n_941_, v___x_942_);
                                        if v___x_943_ == 0 {
                                            leanh::lean_dec(v_n_941_);
                                            v___x_944_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                                            return v___x_944_;
                                        } else {
                                            v_n_945_ = l_Lean_TSyntax_getNat(v_n_941_);
                                            leanh::lean_dec(v_n_941_);
                                            v___f_946_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___lam__3___boxed as *mut core::ffi::c_void, 2, 1);
                                            leanh::lean_closure_set(v___f_946_, 0, v_n_945_);
                                            v___x_947_ =
                                                leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                            leanh::lean_ctor_set(v___x_947_, 0, v___f_946_);
                                            v___x_948_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(v___x_948_, 0, v___x_947_);
                                            return v___x_948_;
                                        }
                                    }
                                } else {
                                    v___x_949_ = leanh::lean_unsigned_to_nat(1);
                                    v_a_950_ = l_Lean_Syntax_getArg(v_filter_838_, v___x_949_);
                                    leanh::lean_dec(v_filter_838_);
                                    v_filter_838_ = v_a_950_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                v___x_952_ = leanh::lean_unsigned_to_nat(1);
                                v_a_953_ = l_Lean_Syntax_getArg(v_filter_838_, v___x_952_);
                                leanh::lean_dec(v_filter_838_);
                                v___x_954_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_953_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
                                if leanh::lean_obj_tag(v___x_954_) == 0 {
                                    v_a_955_ = leanh::lean_ctor_get(v___x_954_, 0);
                                    v_isSharedCheck_963_ =
                                        (!leanh::lean_is_exclusive(v___x_954_)) as u8;
                                    if v_isSharedCheck_963_ == 0 {
                                        v___x_957_ = v___x_954_;
                                        v_isShared_958_ = v_isSharedCheck_963_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_955_);
                                        leanh::lean_dec(v___x_954_);
                                        v___x_957_ = leanh::lean_box(0);
                                        v_isShared_958_ = v_isSharedCheck_963_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    return v___x_954_;
                                }
                            }
                        } else {
                            v___x_964_ = leanh::lean_unsigned_to_nat(0);
                            v_a_965_ = l_Lean_Syntax_getArg(v_filter_838_, v___x_964_);
                            v___x_966_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_965_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
                            if leanh::lean_obj_tag(v___x_966_) == 0 {
                                v_a_967_ = leanh::lean_ctor_get(v___x_966_, 0);
                                leanh::lean_inc(v_a_967_);
                                leanh::lean_dec_ref_known(v___x_966_, 1);
                                v___x_968_ = leanh::lean_unsigned_to_nat(2);
                                v_b_969_ = l_Lean_Syntax_getArg(v_filter_838_, v___x_968_);
                                leanh::lean_dec(v_filter_838_);
                                v___x_970_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_b_969_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
                                if leanh::lean_obj_tag(v___x_970_) == 0 {
                                    v_a_971_ = leanh::lean_ctor_get(v___x_970_, 0);
                                    v_isSharedCheck_979_ =
                                        (!leanh::lean_is_exclusive(v___x_970_)) as u8;
                                    if v_isSharedCheck_979_ == 0 {
                                        v___x_973_ = v___x_970_;
                                        v_isShared_974_ = v_isSharedCheck_979_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_971_);
                                        leanh::lean_dec(v___x_970_);
                                        v___x_973_ = leanh::lean_box(0);
                                        v_isShared_974_ = v_isSharedCheck_979_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_967_);
                                    return v___x_970_;
                                }
                            } else {
                                leanh::lean_dec(v_filter_838_);
                                return v___x_966_;
                            }
                        }
                    } else {
                        v___x_980_ = leanh::lean_unsigned_to_nat(0);
                        v_a_981_ = l_Lean_Syntax_getArg(v_filter_838_, v___x_980_);
                        v___x_982_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_a_981_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
                        if leanh::lean_obj_tag(v___x_982_) == 0 {
                            v_a_983_ = leanh::lean_ctor_get(v___x_982_, 0);
                            leanh::lean_inc(v_a_983_);
                            leanh::lean_dec_ref_known(v___x_982_, 1);
                            v___x_984_ = leanh::lean_unsigned_to_nat(2);
                            v_b_985_ = l_Lean_Syntax_getArg(v_filter_838_, v___x_984_);
                            leanh::lean_dec(v_filter_838_);
                            v___x_986_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(v_b_985_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
                            if leanh::lean_obj_tag(v___x_986_) == 0 {
                                v_a_987_ = leanh::lean_ctor_get(v___x_986_, 0);
                                v_isSharedCheck_995_ =
                                    (!leanh::lean_is_exclusive(v___x_986_)) as u8;
                                if v_isSharedCheck_995_ == 0 {
                                    v___x_989_ = v___x_986_;
                                    v_isShared_990_ = v_isSharedCheck_995_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_987_);
                                    leanh::lean_dec(v___x_986_);
                                    v___x_989_ = leanh::lean_box(0);
                                    v_isShared_990_ = v_isSharedCheck_995_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_983_);
                                return v___x_986_;
                            }
                        } else {
                            leanh::lean_dec(v_filter_838_);
                            return v___x_982_;
                        }
                    }
                } else {
                    v___x_996_ = leanh::lean_unsigned_to_nat(0);
                    v___x_997_ = l_Lean_Syntax_getArg(v_filter_838_, v___x_996_);
                    leanh::lean_dec(v_filter_838_);
                    v___x_998_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__33;
                    leanh::lean_inc(v___x_997_);
                    v___x_999_ = l_Lean_Syntax_isOfKind(v___x_997_, v___x_998_);
                    if v___x_999_ == 0 {
                        leanh::lean_dec(v___x_997_);
                        v___x_1000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__0___redArg();
                        return v___x_1000_;
                    } else {
                        v___x_1001_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__34;
                        v___x_1002_ = 0;
                        leanh::lean_inc(v___x_997_);
                        v___x_1003_ = l_Lean_Elab_Term_resolveId_x3f(
                            v___x_997_,
                            v___x_1001_,
                            v___x_1002_,
                            v_a_841_,
                            v_a_842_,
                            v_a_843_,
                            v_a_844_,
                            v_a_845_,
                            v_a_846_,
                        );
                        if leanh::lean_obj_tag(v___x_1003_) == 0 {
                            v_a_1004_ = leanh::lean_ctor_get(v___x_1003_, 0);
                            v_isSharedCheck_1038_ =
                                (!leanh::lean_is_exclusive(v___x_1003_)) as u8;
                            if v_isSharedCheck_1038_ == 0 {
                                v___x_1006_ = v___x_1003_;
                                v_isShared_1007_ = v_isSharedCheck_1038_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1004_);
                                leanh::lean_dec(v___x_1003_);
                                v___x_1006_ = leanh::lean_box(0);
                                v_isShared_1007_ = v_isSharedCheck_1038_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_997_);
                            v_a_1039_ = leanh::lean_ctor_get(v___x_1003_, 0);
                            v_isSharedCheck_1046_ =
                                (!leanh::lean_is_exclusive(v___x_1003_)) as u8;
                            if v_isSharedCheck_1046_ == 0 {
                                v___x_1041_ = v___x_1003_;
                                v_isShared_1042_ = v_isSharedCheck_1046_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1039_);
                                leanh::lean_dec(v___x_1003_);
                                v___x_1041_ = leanh::lean_box(0);
                                v_isShared_1042_ = v_isSharedCheck_1046_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_959_ = leanh::lean_alloc_ctor(6, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_959_, 0, v_a_955_);
                if v_isShared_958_ == 0 {
                    leanh::lean_ctor_set(v___x_957_, 0, v___x_959_);
                    v___x_961_ = v___x_957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
                    v___x_961_ = v_reuseFailAlloc_962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_961_;
            }
            3 => {
                v___x_975_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_975_, 0, v_a_967_);
                leanh::lean_ctor_set(v___x_975_, 1, v_a_971_);
                if v_isShared_974_ == 0 {
                    leanh::lean_ctor_set(v___x_973_, 0, v___x_975_);
                    v___x_977_ = v___x_973_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_978_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
                    v___x_977_ = v_reuseFailAlloc_978_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_977_;
            }
            5 => {
                v___x_991_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_991_, 0, v_a_983_);
                leanh::lean_ctor_set(v___x_991_, 1, v_a_987_);
                if v_isShared_990_ == 0 {
                    leanh::lean_ctor_set(v___x_989_, 0, v___x_991_);
                    v___x_993_ = v___x_989_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_994_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
                    v___x_993_ = v_reuseFailAlloc_994_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_993_;
            }
            7 => {
                if leanh::lean_obj_tag(v_a_1004_) == 1 {
                    v_val_1019_ = leanh::lean_ctor_get(v_a_1004_, 0);
                    v_isSharedCheck_1037_ = (!leanh::lean_is_exclusive(v_a_1004_)) as u8;
                    if v_isSharedCheck_1037_ == 0 {
                        v___x_1021_ = v_a_1004_;
                        v_isShared_1022_ = v_isSharedCheck_1037_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1019_);
                        leanh::lean_dec(v_a_1004_);
                        v___x_1021_ = leanh::lean_box(0);
                        v_isShared_1022_ = v_isSharedCheck_1037_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1006_);
                    leanh::lean_dec(v_a_1004_);
                    v___y_1009_ = v_a_839_;
                    v___y_1010_ = v_a_840_;
                    v___y_1011_ = v_a_841_;
                    v___y_1012_ = v_a_842_;
                    v___y_1013_ = v_a_843_;
                    v___y_1014_ = v_a_844_;
                    v___y_1015_ = v_a_845_;
                    v___y_1016_ = v_a_846_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1017_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36_once), _init_l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___closed__36);
                v___x_1018_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v___x_997_, v___x_1017_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
                leanh::lean_dec(v___x_997_);
                return v___x_1018_;
            }
            9 => match leanh::lean_obj_tag(v_val_1019_) {
                4 => {
                    leanh::lean_dec(v___x_997_);
                    v_declName_1023_ = leanh::lean_ctor_get(v_val_1019_, 0);
                    leanh::lean_inc(v_declName_1023_);
                    leanh::lean_dec_ref_known(v_val_1019_, 2);
                    if v_isShared_1022_ == 0 {
                        leanh::lean_ctor_set(v___x_1021_, 0, v_declName_1023_);
                        v___x_1025_ = v___x_1021_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1029_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_declName_1023_);
                        v___x_1025_ = v_reuseFailAlloc_1029_;
                        state = 10;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_dec(v___x_997_);
                    v_fvarId_1030_ = leanh::lean_ctor_get(v_val_1019_, 0);
                    leanh::lean_inc(v_fvarId_1030_);
                    leanh::lean_dec_ref_known(v_val_1019_, 1);
                    if v_isShared_1022_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1021_, 2);
                        leanh::lean_ctor_set(v___x_1021_, 0, v_fvarId_1030_);
                        v___x_1032_ = v___x_1021_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1036_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_fvarId_1030_);
                        v___x_1032_ = v_reuseFailAlloc_1036_;
                        state = 12;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_1021_);
                    leanh::lean_dec(v_val_1019_);
                    leanh::lean_del_object(v___x_1006_);
                    v___y_1009_ = v_a_839_;
                    v___y_1010_ = v_a_840_;
                    v___y_1011_ = v_a_841_;
                    v___y_1012_ = v_a_842_;
                    v___y_1013_ = v_a_843_;
                    v___y_1014_ = v_a_844_;
                    v___y_1015_ = v_a_845_;
                    v___y_1016_ = v_a_846_;
                    state = 8;
                    continue;
                }
            },
            10 => {
                if v_isShared_1007_ == 0 {
                    leanh::lean_ctor_set(v___x_1006_, 0, v___x_1025_);
                    v___x_1027_ = v___x_1006_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1028_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
                    v___x_1027_ = v_reuseFailAlloc_1028_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1027_;
            }
            12 => {
                if v_isShared_1007_ == 0 {
                    leanh::lean_ctor_set(v___x_1006_, 0, v___x_1032_);
                    v___x_1034_ = v___x_1006_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1035_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
                    v___x_1034_ = v_reuseFailAlloc_1035_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1034_;
            }
            14 => {
                if v_isShared_1042_ == 0 {
                    v___x_1044_ = v___x_1041_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1045_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
                    v___x_1044_ = v_reuseFailAlloc_1045_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go___boxed(
    mut v_filter_1047_: *mut leanh::LeanObject,
    mut v_a_1048_: *mut leanh::LeanObject,
    mut v_a_1049_: *mut leanh::LeanObject,
    mut v_a_1050_: *mut leanh::LeanObject,
    mut v_a_1051_: *mut leanh::LeanObject,
    mut v_a_1052_: *mut leanh::LeanObject,
    mut v_a_1053_: *mut leanh::LeanObject,
    mut v_a_1054_: *mut leanh::LeanObject,
    mut v_a_1055_: *mut leanh::LeanObject,
    mut v_a_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ = l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(
        v_filter_1047_,
        v_a_1048_,
        v_a_1049_,
        v_a_1050_,
        v_a_1051_,
        v_a_1052_,
        v_a_1053_,
        v_a_1054_,
        v_a_1055_,
    );
    leanh::lean_dec(v_a_1055_);
    leanh::lean_dec_ref(v_a_1054_);
    leanh::lean_dec(v_a_1053_);
    leanh::lean_dec_ref(v_a_1052_);
    leanh::lean_dec(v_a_1051_);
    leanh::lean_dec_ref(v_a_1050_);
    leanh::lean_dec(v_a_1049_);
    leanh::lean_dec_ref(v_a_1048_);
    return v_res_1057_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(
    mut v_00_u03b1_1058_: *mut leanh::LeanObject,
    mut v_ref_1059_: *mut leanh::LeanObject,
    mut v_msg_1060_: *mut leanh::LeanObject,
    mut v___y_1061_: *mut leanh::LeanObject,
    mut v___y_1062_: *mut leanh::LeanObject,
    mut v___y_1063_: *mut leanh::LeanObject,
    mut v___y_1064_: *mut leanh::LeanObject,
    mut v___y_1065_: *mut leanh::LeanObject,
    mut v___y_1066_: *mut leanh::LeanObject,
    mut v___y_1067_: *mut leanh::LeanObject,
    mut v___y_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___redArg(v_ref_1059_, v_msg_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
    return v___x_1070_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1___boxed(
    mut v_00_u03b1_1071_: *mut leanh::LeanObject,
    mut v_ref_1072_: *mut leanh::LeanObject,
    mut v_msg_1073_: *mut leanh::LeanObject,
    mut v___y_1074_: *mut leanh::LeanObject,
    mut v___y_1075_: *mut leanh::LeanObject,
    mut v___y_1076_: *mut leanh::LeanObject,
    mut v___y_1077_: *mut leanh::LeanObject,
    mut v___y_1078_: *mut leanh::LeanObject,
    mut v___y_1079_: *mut leanh::LeanObject,
    mut v___y_1080_: *mut leanh::LeanObject,
    mut v___y_1081_: *mut leanh::LeanObject,
    mut v___y_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1(v_00_u03b1_1071_, v_ref_1072_, v_msg_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
    leanh::lean_dec(v___y_1081_);
    leanh::lean_dec_ref(v___y_1080_);
    leanh::lean_dec(v___y_1079_);
    leanh::lean_dec_ref(v___y_1078_);
    leanh::lean_dec(v___y_1077_);
    leanh::lean_dec_ref(v___y_1076_);
    leanh::lean_dec(v___y_1075_);
    leanh::lean_dec_ref(v___y_1074_);
    leanh::lean_dec(v_ref_1072_);
    return v_res_1083_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(
    mut v_00_u03b1_1084_: *mut leanh::LeanObject,
    mut v_msg_1085_: *mut leanh::LeanObject,
    mut v___y_1086_: *mut leanh::LeanObject,
    mut v___y_1087_: *mut leanh::LeanObject,
    mut v___y_1088_: *mut leanh::LeanObject,
    mut v___y_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
    mut v___y_1091_: *mut leanh::LeanObject,
    mut v___y_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1095_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___redArg(v_msg_1085_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
    return v___x_1095_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1___boxed(
    mut v_00_u03b1_1096_: *mut leanh::LeanObject,
    mut v_msg_1097_: *mut leanh::LeanObject,
    mut v___y_1098_: *mut leanh::LeanObject,
    mut v___y_1099_: *mut leanh::LeanObject,
    mut v___y_1100_: *mut leanh::LeanObject,
    mut v___y_1101_: *mut leanh::LeanObject,
    mut v___y_1102_: *mut leanh::LeanObject,
    mut v___y_1103_: *mut leanh::LeanObject,
    mut v___y_1104_: *mut leanh::LeanObject,
    mut v___y_1105_: *mut leanh::LeanObject,
    mut v___y_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go_spec__1_spec__1(v_00_u03b1_1096_, v_msg_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
    leanh::lean_dec(v___y_1105_);
    leanh::lean_dec_ref(v___y_1104_);
    leanh::lean_dec(v___y_1103_);
    leanh::lean_dec_ref(v___y_1102_);
    leanh::lean_dec(v___y_1101_);
    leanh::lean_dec_ref(v___y_1100_);
    leanh::lean_dec(v___y_1099_);
    leanh::lean_dec_ref(v___y_1098_);
    return v_res_1107_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabFilter(
    mut v_filter_x3f_1108_: *mut leanh::LeanObject,
    mut v_a_1109_: *mut leanh::LeanObject,
    mut v_a_1110_: *mut leanh::LeanObject,
    mut v_a_1111_: *mut leanh::LeanObject,
    mut v_a_1112_: *mut leanh::LeanObject,
    mut v_a_1113_: *mut leanh::LeanObject,
    mut v_a_1114_: *mut leanh::LeanObject,
    mut v_a_1115_: *mut leanh::LeanObject,
    mut v_a_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_filter_x3f_1108_) == 1 {
        let mut v_val_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1118_ = leanh::lean_ctor_get(v_filter_x3f_1108_, 0);
        leanh::lean_inc(v_val_1118_);
        leanh::lean_dec_ref_known(v_filter_x3f_1108_, 1);
        v___x_1119_ =
            l___private_Lean_Elab_Tactic_Grind_Filter_0__Lean_Elab_Tactic_Grind_elabFilter_go(
                v_val_1118_,
                v_a_1109_,
                v_a_1110_,
                v_a_1111_,
                v_a_1112_,
                v_a_1113_,
                v_a_1114_,
                v_a_1115_,
                v_a_1116_,
            );
        return v___x_1119_;
    } else {
        let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_filter_x3f_1108_);
        v___x_1120_ = leanh::lean_box(0);
        v___x_1121_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1121_, 0, v___x_1120_);
        return v___x_1121_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabFilter___boxed(
    mut v_filter_x3f_1122_: *mut leanh::LeanObject,
    mut v_a_1123_: *mut leanh::LeanObject,
    mut v_a_1124_: *mut leanh::LeanObject,
    mut v_a_1125_: *mut leanh::LeanObject,
    mut v_a_1126_: *mut leanh::LeanObject,
    mut v_a_1127_: *mut leanh::LeanObject,
    mut v_a_1128_: *mut leanh::LeanObject,
    mut v_a_1129_: *mut leanh::LeanObject,
    mut v_a_1130_: *mut leanh::LeanObject,
    mut v_a_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1132_ = l_Lean_Elab_Tactic_Grind_elabFilter(
        v_filter_x3f_1122_,
        v_a_1123_,
        v_a_1124_,
        v_a_1125_,
        v_a_1126_,
        v_a_1127_,
        v_a_1128_,
        v_a_1129_,
        v_a_1130_,
    );
    leanh::lean_dec(v_a_1130_);
    leanh::lean_dec_ref(v_a_1129_);
    leanh::lean_dec(v_a_1128_);
    leanh::lean_dec_ref(v_a_1127_);
    leanh::lean_dec(v_a_1126_);
    leanh::lean_dec_ref(v_a_1125_);
    leanh::lean_dec(v_a_1124_);
    leanh::lean_dec_ref(v_a_1123_);
    return v_res_1132_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_Filter(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_Filter(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_Filter(
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
    res = initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
}