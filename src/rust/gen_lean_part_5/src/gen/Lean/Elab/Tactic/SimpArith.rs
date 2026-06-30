// Lean compiler output
// Module: Lean.Elab.Tactic.SimpArith
// Imports: Lean.Elab.Tactic.Simp Lean.Meta.Tactic.TryThis
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_dec_lt, lean_st_ref_get,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_unsetTrailing;
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_setKind, l_Lean_mkAtom, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::l_Lean_Syntax_setArg;
use crate::r#gen::Lean::Elab::Tactic::Basic::l_Lean_Elab_Tactic_tacticElabAttribute;
use crate::r#gen::Lean::Elab::Tactic::Simp::{
    initialize_Lean_Elab_Tactic_Simp, runtime_initialize_Lean_Elab_Tactic_Simp,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_nil, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__0_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__3_value) as *mut leanh::LeanObject,10138443044734372301 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__5_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 111, 115, 67, 111, 110, 102, 105, 103, 73, 116, 101, 109, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__5_value) as *mut leanh::LeanObject,9555431800314169832 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [43, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8_value) as *mut leanh::LeanObject,3738010876686032200 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0_value) as *mut leanh::LeanObject,10759351130620427500 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__0_value) as *mut leanh::LeanObject,16145843736367156323 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [84, 114, 121, 32, 116, 104, 101, 115, 101, 58, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpArith___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Elab_Tactic_evalSimpArith___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArith___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_evalSimpArith___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArith___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArith___closed__0_value)
                as *mut leanh::LeanObject,
            12783917532758215986 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpArith___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArith___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpArith___closed__2_value: leanh::LeanStringObject<164> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 164,
        m_capacity: 164,
        m_length: 163,
        m_data: [
            96, 115, 105, 109, 112, 95, 97, 114, 105, 116, 104, 96, 32, 104, 97, 115, 32, 98, 101,
            101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 46, 32, 73, 116, 32, 119,
            97, 115, 32, 97, 32, 115, 104, 111, 114, 116, 104, 97, 110, 100, 32, 102, 111, 114, 32,
            96, 115, 105, 109, 112, 32, 43, 97, 114, 105, 116, 104, 32, 43, 100, 101, 99, 105, 100,
            101, 96, 44, 32, 98, 117, 116, 32, 109, 111, 115, 116, 32, 111, 102, 32, 116, 104, 101,
            32, 116, 105, 109, 101, 44, 32, 96, 43, 100, 101, 99, 105, 100, 101, 96, 32, 119, 97,
            115, 32, 114, 101, 100, 117, 110, 100, 97, 110, 116, 32, 115, 105, 110, 99, 101, 32,
            115, 105, 109, 112, 114, 111, 99, 115, 32, 104, 97, 118, 101, 32, 98, 101, 101, 110,
            32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 46, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalSimpArith___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArith___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalSimpArith___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalSimpArith___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__0_value) as *mut leanh::LeanObject,14480302902855741354 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__3_value) as *mut leanh::LeanObject,5557944076692407353 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0_value:
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
    m_data: [115, 105, 109, 112, 33, 0],
};
static mut l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__1_value:
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
        115, 105, 109, 112, 65, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17342550436400123219 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3_value:
    leanh::LeanStringObject<166> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 166,
    m_capacity: 166,
    m_length: 165,
    m_data: [
        96, 115, 105, 109, 112, 95, 97, 114, 105, 116, 104, 33, 96, 32, 104, 97, 115, 32, 98, 101,
        101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 46, 32, 73, 116, 32, 119, 97,
        115, 32, 97, 32, 115, 104, 111, 114, 116, 104, 97, 110, 100, 32, 102, 111, 114, 32, 96,
        115, 105, 109, 112, 33, 32, 43, 97, 114, 105, 116, 104, 32, 43, 100, 101, 99, 105, 100,
        101, 96, 44, 32, 98, 117, 116, 32, 109, 111, 115, 116, 32, 111, 102, 32, 116, 104, 101, 32,
        116, 105, 109, 101, 44, 32, 96, 43, 100, 101, 99, 105, 100, 101, 96, 32, 119, 97, 115, 32,
        114, 101, 100, 117, 110, 100, 97, 110, 116, 32, 115, 105, 110, 99, 101, 32, 115, 105, 109,
        112, 114, 111, 99, 115, 32, 104, 97, 118, 101, 32, 98, 101, 101, 110, 32, 105, 109, 112,
        108, 101, 109, 101, 110, 116, 101, 100, 46, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 105, 109, 112, 65, 114, 105, 116, 104, 66, 97, 110, 103, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__0_value) as *mut leanh::LeanObject,4672287204283619115 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 65, 114, 105, 116, 104, 66, 97, 110, 103, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__2_value) as *mut leanh::LeanObject,9878999245578620784 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 105, 109, 112, 95, 97, 108, 108, 0],
};
static mut l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__1_value:
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
    m_data: [115, 105, 109, 112, 65, 108, 108, 0],
};
static mut l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        17985617252278808837 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3_value:
    leanh::LeanStringObject<172> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 172,
    m_capacity: 172,
    m_length: 171,
    m_data: [
        96, 115, 105, 109, 112, 95, 97, 108, 108, 95, 97, 114, 105, 116, 104, 96, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 46, 32, 73, 116,
        32, 119, 97, 115, 32, 97, 32, 115, 104, 111, 114, 116, 104, 97, 110, 100, 32, 102, 111,
        114, 32, 96, 115, 105, 109, 112, 95, 97, 108, 108, 32, 43, 97, 114, 105, 116, 104, 32, 43,
        100, 101, 99, 105, 100, 101, 96, 44, 32, 98, 117, 116, 32, 109, 111, 115, 116, 32, 111,
        102, 32, 116, 104, 101, 32, 116, 105, 109, 101, 44, 32, 96, 43, 100, 101, 99, 105, 100,
        101, 96, 32, 119, 97, 115, 32, 114, 101, 100, 117, 110, 100, 97, 110, 116, 32, 115, 105,
        110, 99, 101, 32, 115, 105, 109, 112, 114, 111, 99, 115, 32, 104, 97, 118, 101, 32, 98,
        101, 101, 110, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 46, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 105, 109, 112, 65, 108, 108, 65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__0_value) as *mut leanh::LeanObject,3392380392473414360 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 65, 108, 108, 65, 114, 105, 116, 104, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__2_value) as *mut leanh::LeanObject,17865150110312068327 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0_value:
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
    m_data: [115, 105, 109, 112, 95, 97, 108, 108, 33, 0],
};
static mut l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__1_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        115, 105, 109, 112, 65, 108, 108, 65, 117, 116, 111, 85, 110, 102, 111, 108, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value:
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
            l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        10659525765844864087 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3_value:
    leanh::LeanStringObject<174> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 174,
    m_capacity: 174,
    m_length: 173,
    m_data: [
        96, 115, 105, 109, 112, 95, 97, 108, 108, 95, 97, 114, 105, 116, 104, 33, 96, 32, 104, 97,
        115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 46, 32, 73,
        116, 32, 119, 97, 115, 32, 97, 32, 115, 104, 111, 114, 116, 104, 97, 110, 100, 32, 102,
        111, 114, 32, 96, 115, 105, 109, 112, 95, 97, 108, 108, 33, 32, 43, 97, 114, 105, 116, 104,
        32, 43, 100, 101, 99, 105, 100, 101, 96, 44, 32, 98, 117, 116, 32, 109, 111, 115, 116, 32,
        111, 102, 32, 116, 104, 101, 32, 116, 105, 109, 101, 44, 32, 96, 43, 100, 101, 99, 105,
        100, 101, 96, 32, 119, 97, 115, 32, 114, 101, 100, 117, 110, 100, 97, 110, 116, 32, 115,
        105, 110, 99, 101, 32, 115, 105, 109, 112, 114, 111, 99, 115, 32, 104, 97, 118, 101, 32,
        98, 101, 101, 110, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 46, 0,
    ],
};
static mut l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 109, 112, 65, 108, 108, 65, 114, 105, 116, 104, 66, 97, 110, 103, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__0_value) as *mut leanh::LeanObject,3546702534615090220 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 65, 108, 108, 65, 114, 105, 116, 104, 66, 97, 110, 103, 0]};
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__2_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__2_value) as *mut leanh::LeanObject,5825315192071176672 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(
    mut v_stx_541_: *mut leanh::LeanObject,
    mut v_item_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_optConfig_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_554_: u8 = 0;
    let mut v_v_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_unused_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_543_ = leanh::lean_unsigned_to_nat(1);
                v_optConfig_544_ = l_Lean_Syntax_getArg(v_stx_541_, v___x_543_);
                if leanh::lean_obj_tag(v_optConfig_544_) == 1 {
                    v_info_545_ = leanh::lean_ctor_get(v_optConfig_544_, 0);
                    leanh::lean_inc(v_info_545_);
                    v_kind_546_ = leanh::lean_ctor_get(v_optConfig_544_, 1);
                    leanh::lean_inc(v_kind_546_);
                    v_args_547_ = leanh::lean_ctor_get(v_optConfig_544_, 2);
                    leanh::lean_inc_ref(v_args_547_);
                    v___x_548_ = leanh::lean_unsigned_to_nat(0);
                    v___x_549_ = lean_array_get_size(v_args_547_);
                    v___x_550_ = lean_nat_dec_lt(v___x_548_, v___x_549_);
                    if v___x_550_ == 0 {
                        leanh::lean_dec_ref(v_args_547_);
                        leanh::lean_dec(v_kind_546_);
                        leanh::lean_dec(v_info_545_);
                        leanh::lean_dec(v_item_542_);
                        v___x_551_ = l_Lean_Syntax_setArg(v_stx_541_, v___x_543_, v_optConfig_544_);
                        return v___x_551_;
                    } else {
                        v_isSharedCheck_570_ =
                            (!leanh::lean_is_exclusive(v_optConfig_544_)) as u8;
                        if v_isSharedCheck_570_ == 0 {
                            v_unused_571_ = leanh::lean_ctor_get(v_optConfig_544_, 2);
                            leanh::lean_dec(v_unused_571_);
                            v_unused_572_ = leanh::lean_ctor_get(v_optConfig_544_, 1);
                            leanh::lean_dec(v_unused_572_);
                            v_unused_573_ = leanh::lean_ctor_get(v_optConfig_544_, 0);
                            leanh::lean_dec(v_unused_573_);
                            v___x_553_ = v_optConfig_544_;
                            v_isShared_554_ = v_isSharedCheck_570_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_optConfig_544_);
                            v___x_553_ = leanh::lean_box(0);
                            v_isShared_554_ = v_isSharedCheck_570_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_item_542_);
                    v___x_574_ = l_Lean_Syntax_setArg(v_stx_541_, v___x_543_, v_optConfig_544_);
                    return v___x_574_;
                }
            }
            1 => {
                v_v_555_ = lean_array_fget(v_args_547_, v___x_548_);
                v___x_556_ = leanh::lean_box(0);
                v_xs_x27_557_ = lean_array_fset(v_args_547_, v___x_548_, v___x_556_);
                v___x_558_ = lean_mk_empty_array_with_capacity(v___x_543_);
                v___x_559_ = lean_array_push(v___x_558_, v_item_542_);
                v___x_560_ = l_Lean_Syntax_getArgs(v_v_555_);
                leanh::lean_dec(v_v_555_);
                v___x_561_ = l_Array_append___redArg(v___x_559_, v___x_560_);
                leanh::lean_dec_ref(v___x_560_);
                v___x_562_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem___closed__1;
                v___x_563_ = leanh::lean_box(2);
                if v_isShared_554_ == 0 {
                    leanh::lean_ctor_set(v___x_553_, 2, v___x_561_);
                    leanh::lean_ctor_set(v___x_553_, 1, v___x_562_);
                    leanh::lean_ctor_set(v___x_553_, 0, v___x_563_);
                    v___x_565_ = v___x_553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_569_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_569_, 2, v___x_561_);
                    v___x_565_ = v_reuseFailAlloc_569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_566_ = lean_array_fset(v_xs_x27_557_, v___x_548_, v___x_565_);
                v___x_567_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_567_, 0, v_info_545_);
                leanh::lean_ctor_set(v___x_567_, 1, v_kind_546_);
                leanh::lean_ctor_set(v___x_567_, 2, v___x_566_);
                v___x_568_ = l_Lean_Syntax_setArg(v_stx_541_, v___x_543_, v___x_567_);
                return v___x_568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__8;
    v___x_593_ = l_String_toRawSubstring_x27(v___x_592_);
    return v___x_593_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(
    mut v_stx_596_: *mut leanh::LeanObject,
    mut v_a_597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: u8 = 0;
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_599_ = leanh::lean_ctor_get(v_a_597_, 5);
    v___x_600_ = 0;
    v___x_601_ = l_Lean_SourceInfo_fromRef(v_ref_599_, v___x_600_);
    v___x_602_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4;
    v___x_603_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6;
    v___x_604_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7;
    leanh::lean_inc_n(v___x_601_, 3);
    v___x_605_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_605_, 0, v___x_601_);
    leanh::lean_ctor_set(v___x_605_, 1, v___x_604_);
    v___x_606_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9_once), _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__9);
    v___x_607_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__10;
    v___x_608_ = leanh::lean_box(0);
    v___x_609_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_609_, 0, v___x_601_);
    leanh::lean_ctor_set(v___x_609_, 1, v___x_606_);
    leanh::lean_ctor_set(v___x_609_, 2, v___x_607_);
    leanh::lean_ctor_set(v___x_609_, 3, v___x_608_);
    v___x_610_ = l_Lean_Syntax_node2(v___x_601_, v___x_603_, v___x_605_, v___x_609_);
    v___x_611_ = l_Lean_Syntax_node1(v___x_601_, v___x_602_, v___x_610_);
    v___x_612_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(
        v_stx_596_, v___x_611_,
    );
    v___x_613_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_613_, 0, v___x_612_);
    return v___x_613_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___boxed(
    mut v_stx_614_: *mut leanh::LeanObject,
    mut v_a_615_: *mut leanh::LeanObject,
    mut v_a_616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_617_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(
        v_stx_614_, v_a_615_,
    );
    leanh::lean_dec_ref(v_a_615_);
    return v_res_617_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(
    mut v_stx_618_: *mut leanh::LeanObject,
    mut v_a_619_: *mut leanh::LeanObject,
    mut v_a_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_622_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(
        v_stx_618_, v_a_619_,
    );
    return v___x_622_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___boxed(
    mut v_stx_623_: *mut leanh::LeanObject,
    mut v_a_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
    mut v_a_626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_627_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(
        v_stx_623_, v_a_624_, v_a_625_,
    );
    leanh::lean_dec(v_a_625_);
    leanh::lean_dec_ref(v_a_624_);
    return v_res_627_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_629_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__0;
    v___x_630_ = l_String_toRawSubstring_x27(v___x_629_);
    return v___x_630_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(
    mut v_stx_633_: *mut leanh::LeanObject,
    mut v_a_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: u8 = 0;
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_636_ = leanh::lean_ctor_get(v_a_634_, 5);
    v___x_637_ = 0;
    v___x_638_ = l_Lean_SourceInfo_fromRef(v_ref_636_, v___x_637_);
    v___x_639_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__4;
    v___x_640_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__6;
    v___x_641_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg___closed__7;
    leanh::lean_inc_n(v___x_638_, 3);
    v___x_642_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_642_, 0, v___x_638_);
    leanh::lean_ctor_set(v___x_642_, 1, v___x_641_);
    v___x_643_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__1);
    v___x_644_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___closed__2;
    v___x_645_ = leanh::lean_box(0);
    v___x_646_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_646_, 0, v___x_638_);
    leanh::lean_ctor_set(v___x_646_, 1, v___x_643_);
    leanh::lean_ctor_set(v___x_646_, 2, v___x_644_);
    leanh::lean_ctor_set(v___x_646_, 3, v___x_645_);
    v___x_647_ = l_Lean_Syntax_node2(v___x_638_, v___x_640_, v___x_642_, v___x_646_);
    v___x_648_ = l_Lean_Syntax_node1(v___x_638_, v___x_639_, v___x_647_);
    v___x_649_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(
        v_stx_633_, v___x_648_,
    );
    v___x_650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_650_, 0, v___x_649_);
    return v___x_650_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg___boxed(
    mut v_stx_651_: *mut leanh::LeanObject,
    mut v_a_652_: *mut leanh::LeanObject,
    mut v_a_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_654_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(
        v_stx_651_, v_a_652_,
    );
    leanh::lean_dec_ref(v_a_652_);
    return v_res_654_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(
    mut v_stx_655_: *mut leanh::LeanObject,
    mut v_a_656_: *mut leanh::LeanObject,
    mut v_a_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(
        v_stx_655_, v_a_656_,
    );
    return v___x_659_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___boxed(
    mut v_stx_660_: *mut leanh::LeanObject,
    mut v_a_661_: *mut leanh::LeanObject,
    mut v_a_662_: *mut leanh::LeanObject,
    mut v_a_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_664_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(
        v_stx_660_, v_a_661_, v_a_662_,
    );
    leanh::lean_dec(v_a_662_);
    leanh::lean_dec_ref(v_a_661_);
    return v_res_664_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(
    mut v_stx_665_: *mut leanh::LeanObject,
    mut v_str_666_: *mut leanh::LeanObject,
    mut v_kind_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stx_668_ = l_Lean_Syntax_setKind(v_stx_665_, v_kind_667_);
    v___x_669_ = leanh::lean_unsigned_to_nat(0);
    v___x_670_ = l_Lean_mkAtom(v_str_666_);
    v___x_671_ = l_Lean_Syntax_setArg(v_stx_668_, v___x_669_, v___x_670_);
    return v___x_671_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(
    mut v_stx_676_: *mut leanh::LeanObject,
    mut v_tokenNew_677_: *mut leanh::LeanObject,
    mut v_kindNew_678_: *mut leanh::LeanObject,
    mut v_a_679_: *mut leanh::LeanObject,
    mut v_a_680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stx_x27_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_x27_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_692_: u8 = 0;
    let mut v_ref_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: u8 = 0;
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_stx_676_);
                v_stx_x27_682_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(
                    v_stx_676_,
                    v_tokenNew_677_,
                    v_kindNew_678_,
                );
                v_stx_x27_683_ = l_Lean_Syntax_unsetTrailing(v_stx_x27_682_);
                leanh::lean_inc(v_stx_x27_683_);
                v___x_684_ =
                    l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(
                        v_stx_x27_683_,
                        v_a_679_,
                    );
                v_a_685_ = leanh::lean_ctor_get(v___x_684_, 0);
                leanh::lean_inc(v_a_685_);
                leanh::lean_dec_ref(v___x_684_);
                v___x_686_ =
                    l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___redArg(
                        v_stx_x27_683_,
                        v_a_679_,
                    );
                v_a_687_ = leanh::lean_ctor_get(v___x_686_, 0);
                leanh::lean_inc(v_a_687_);
                leanh::lean_dec_ref(v___x_686_);
                v___x_688_ =
                    l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___redArg(
                        v_a_687_, v_a_679_,
                    );
                v_a_689_ = leanh::lean_ctor_get(v___x_688_, 0);
                v_isSharedCheck_713_ = (!leanh::lean_is_exclusive(v___x_688_)) as u8;
                if v_isSharedCheck_713_ == 0 {
                    v___x_691_ = v___x_688_;
                    v_isShared_692_ = v_isSharedCheck_713_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_689_);
                    leanh::lean_dec(v___x_688_);
                    v___x_691_ = leanh::lean_box(0);
                    v_isShared_692_ = v_isSharedCheck_713_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_693_ = leanh::lean_ctor_get(v_a_679_, 5);
                v___x_694_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__1;
                v___x_695_ = leanh::lean_unsigned_to_nat(0);
                v___x_696_ = l_Lean_Syntax_getArg(v_stx_676_, v___x_695_);
                leanh::lean_dec(v_stx_676_);
                v___x_697_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_697_, 0, v___x_694_);
                leanh::lean_ctor_set(v___x_697_, 1, v_a_685_);
                v___x_698_ = leanh::lean_box(0);
                v___x_699_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_699_, 0, v___x_697_);
                leanh::lean_ctor_set(v___x_699_, 1, v___x_698_);
                leanh::lean_ctor_set(v___x_699_, 2, v___x_698_);
                leanh::lean_ctor_set(v___x_699_, 3, v___x_698_);
                leanh::lean_ctor_set(v___x_699_, 4, v___x_698_);
                leanh::lean_ctor_set(v___x_699_, 5, v___x_698_);
                v___x_700_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_700_, 0, v___x_694_);
                leanh::lean_ctor_set(v___x_700_, 1, v_a_689_);
                v___x_701_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_701_, 0, v___x_700_);
                leanh::lean_ctor_set(v___x_701_, 1, v___x_698_);
                leanh::lean_ctor_set(v___x_701_, 2, v___x_698_);
                leanh::lean_ctor_set(v___x_701_, 3, v___x_698_);
                leanh::lean_ctor_set(v___x_701_, 4, v___x_698_);
                leanh::lean_ctor_set(v___x_701_, 5, v___x_698_);
                v___x_702_ = leanh::lean_unsigned_to_nat(2);
                v___x_703_ = lean_mk_empty_array_with_capacity(v___x_702_);
                v___x_704_ = lean_array_push(v___x_703_, v___x_699_);
                v___x_705_ = lean_array_push(v___x_704_, v___x_701_);
                leanh::lean_inc(v_ref_693_);
                if v_isShared_692_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_691_, 1);
                    leanh::lean_ctor_set(v___x_691_, 0, v_ref_693_);
                    v___x_707_ = v___x_691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_712_, 0, v_ref_693_);
                    v___x_707_ = v_reuseFailAlloc_712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_708_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___closed__2;
                v___x_709_ = 4;
                v___x_710_ = l_Lean_MessageData_nil;
                v___x_711_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(
                    v___x_696_, v___x_705_, v___x_707_, v___x_708_, v___x_698_, v___x_709_,
                    v___x_710_, v_a_679_, v_a_680_,
                );
                return v___x_711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg___boxed(
    mut v_stx_714_: *mut leanh::LeanObject,
    mut v_tokenNew_715_: *mut leanh::LeanObject,
    mut v_kindNew_716_: *mut leanh::LeanObject,
    mut v_a_717_: *mut leanh::LeanObject,
    mut v_a_718_: *mut leanh::LeanObject,
    mut v_a_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(
        v_stx_714_,
        v_tokenNew_715_,
        v_kindNew_716_,
        v_a_717_,
        v_a_718_,
    );
    leanh::lean_dec(v_a_718_);
    leanh::lean_dec_ref(v_a_717_);
    return v_res_720_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(
    mut v_stx_721_: *mut leanh::LeanObject,
    mut v_tokenNew_722_: *mut leanh::LeanObject,
    mut v_kindNew_723_: *mut leanh::LeanObject,
    mut v_a_724_: *mut leanh::LeanObject,
    mut v_a_725_: *mut leanh::LeanObject,
    mut v_a_726_: *mut leanh::LeanObject,
    mut v_a_727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(
        v_stx_721_,
        v_tokenNew_722_,
        v_kindNew_723_,
        v_a_726_,
        v_a_727_,
    );
    return v___x_729_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___boxed(
    mut v_stx_730_: *mut leanh::LeanObject,
    mut v_tokenNew_731_: *mut leanh::LeanObject,
    mut v_kindNew_732_: *mut leanh::LeanObject,
    mut v_a_733_: *mut leanh::LeanObject,
    mut v_a_734_: *mut leanh::LeanObject,
    mut v_a_735_: *mut leanh::LeanObject,
    mut v_a_736_: *mut leanh::LeanObject,
    mut v_a_737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_738_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(
        v_stx_730_,
        v_tokenNew_731_,
        v_kindNew_732_,
        v_a_733_,
        v_a_734_,
        v_a_735_,
        v_a_736_,
    );
    leanh::lean_dec(v_a_736_);
    leanh::lean_dec_ref(v_a_735_);
    leanh::lean_dec(v_a_734_);
    leanh::lean_dec_ref(v_a_733_);
    return v_res_738_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(
    mut v_msgData_739_: *mut leanh::LeanObject,
    mut v___y_740_: *mut leanh::LeanObject,
    mut v___y_741_: *mut leanh::LeanObject,
    mut v___y_742_: *mut leanh::LeanObject,
    mut v___y_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_745_ = lean_st_ref_get(v___y_743_);
    v_env_746_ = leanh::lean_ctor_get(v___x_745_, 0);
    leanh::lean_inc_ref(v_env_746_);
    leanh::lean_dec(v___x_745_);
    v___x_747_ = lean_st_ref_get(v___y_741_);
    v_mctx_748_ = leanh::lean_ctor_get(v___x_747_, 0);
    leanh::lean_inc_ref(v_mctx_748_);
    leanh::lean_dec(v___x_747_);
    v_lctx_749_ = leanh::lean_ctor_get(v___y_740_, 2);
    v_options_750_ = leanh::lean_ctor_get(v___y_742_, 2);
    leanh::lean_inc_ref(v_options_750_);
    leanh::lean_inc_ref(v_lctx_749_);
    v___x_751_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_751_, 0, v_env_746_);
    leanh::lean_ctor_set(v___x_751_, 1, v_mctx_748_);
    leanh::lean_ctor_set(v___x_751_, 2, v_lctx_749_);
    leanh::lean_ctor_set(v___x_751_, 3, v_options_750_);
    v___x_752_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_752_, 0, v___x_751_);
    leanh::lean_ctor_set(v___x_752_, 1, v_msgData_739_);
    v___x_753_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_753_, 0, v___x_752_);
    return v___x_753_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0___boxed(
    mut v_msgData_754_: *mut leanh::LeanObject,
    mut v___y_755_: *mut leanh::LeanObject,
    mut v___y_756_: *mut leanh::LeanObject,
    mut v___y_757_: *mut leanh::LeanObject,
    mut v___y_758_: *mut leanh::LeanObject,
    mut v___y_759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(v_msgData_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
    leanh::lean_dec(v___y_758_);
    leanh::lean_dec_ref(v___y_757_);
    leanh::lean_dec(v___y_756_);
    leanh::lean_dec_ref(v___y_755_);
    return v_res_760_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(
    mut v_msg_761_: *mut leanh::LeanObject,
    mut v___y_762_: *mut leanh::LeanObject,
    mut v___y_763_: *mut leanh::LeanObject,
    mut v___y_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_772_: u8 = 0;
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_767_ = leanh::lean_ctor_get(v___y_764_, 5);
                v___x_768_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0_spec__0(v_msg_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
                v_a_769_ = leanh::lean_ctor_get(v___x_768_, 0);
                v_isSharedCheck_777_ = (!leanh::lean_is_exclusive(v___x_768_)) as u8;
                if v_isSharedCheck_777_ == 0 {
                    v___x_771_ = v___x_768_;
                    v_isShared_772_ = v_isSharedCheck_777_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_769_);
                    leanh::lean_dec(v___x_768_);
                    v___x_771_ = leanh::lean_box(0);
                    v_isShared_772_ = v_isSharedCheck_777_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_767_);
                v___x_773_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_773_, 0, v_ref_767_);
                leanh::lean_ctor_set(v___x_773_, 1, v_a_769_);
                if v_isShared_772_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_771_, 1);
                    leanh::lean_ctor_set(v___x_771_, 0, v___x_773_);
                    v___x_775_ = v___x_771_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_776_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
                    v___x_775_ = v_reuseFailAlloc_776_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg___boxed(
    mut v_msg_778_: *mut leanh::LeanObject,
    mut v___y_779_: *mut leanh::LeanObject,
    mut v___y_780_: *mut leanh::LeanObject,
    mut v___y_781_: *mut leanh::LeanObject,
    mut v___y_782_: *mut leanh::LeanObject,
    mut v___y_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(
        v_msg_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_,
    );
    leanh::lean_dec(v___y_782_);
    leanh::lean_dec_ref(v___y_781_);
    leanh::lean_dec(v___y_780_);
    leanh::lean_dec_ref(v___y_779_);
    return v_res_784_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpArith___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = l_Lean_Elab_Tactic_evalSimpArith___closed__2;
    v___x_793_ = l_Lean_stringToMessageData(v___x_792_);
    return v___x_793_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpArith(
    mut v_stx_794_: *mut leanh::LeanObject,
    mut v_a_795_: *mut leanh::LeanObject,
    mut v_a_796_: *mut leanh::LeanObject,
    mut v_a_797_: *mut leanh::LeanObject,
    mut v_a_798_: *mut leanh::LeanObject,
    mut v_a_799_: *mut leanh::LeanObject,
    mut v_a_800_: *mut leanh::LeanObject,
    mut v_a_801_: *mut leanh::LeanObject,
    mut v_a_802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_Elab_Tactic_evalSimpArith___closed__0;
    v___x_805_ = l_Lean_Elab_Tactic_evalSimpArith___closed__1;
    v___x_806_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(
        v_stx_794_, v___x_804_, v___x_805_, v_a_801_, v_a_802_,
    );
    if leanh::lean_obj_tag(v___x_806_) == 0 {
        let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_806_, 1);
        v___x_807_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpArith___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpArith___closed__3_once),
            _init_l_Lean_Elab_Tactic_evalSimpArith___closed__3,
        );
        v___x_808_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(
            v___x_807_, v_a_799_, v_a_800_, v_a_801_, v_a_802_,
        );
        return v___x_808_;
    } else {
        return v___x_806_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpArith___boxed(
    mut v_stx_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
    mut v_a_814_: *mut leanh::LeanObject,
    mut v_a_815_: *mut leanh::LeanObject,
    mut v_a_816_: *mut leanh::LeanObject,
    mut v_a_817_: *mut leanh::LeanObject,
    mut v_a_818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Lean_Elab_Tactic_evalSimpArith(
        v_stx_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_,
    );
    leanh::lean_dec(v_a_817_);
    leanh::lean_dec_ref(v_a_816_);
    leanh::lean_dec(v_a_815_);
    leanh::lean_dec_ref(v_a_814_);
    leanh::lean_dec(v_a_813_);
    leanh::lean_dec_ref(v_a_812_);
    leanh::lean_dec(v_a_811_);
    leanh::lean_dec_ref(v_a_810_);
    return v_res_819_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(
    mut v_00_u03b1_820_: *mut leanh::LeanObject,
    mut v_msg_821_: *mut leanh::LeanObject,
    mut v___y_822_: *mut leanh::LeanObject,
    mut v___y_823_: *mut leanh::LeanObject,
    mut v___y_824_: *mut leanh::LeanObject,
    mut v___y_825_: *mut leanh::LeanObject,
    mut v___y_826_: *mut leanh::LeanObject,
    mut v___y_827_: *mut leanh::LeanObject,
    mut v___y_828_: *mut leanh::LeanObject,
    mut v___y_829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(
        v_msg_821_, v___y_826_, v___y_827_, v___y_828_, v___y_829_,
    );
    return v___x_831_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___boxed(
    mut v_00_u03b1_832_: *mut leanh::LeanObject,
    mut v_msg_833_: *mut leanh::LeanObject,
    mut v___y_834_: *mut leanh::LeanObject,
    mut v___y_835_: *mut leanh::LeanObject,
    mut v___y_836_: *mut leanh::LeanObject,
    mut v___y_837_: *mut leanh::LeanObject,
    mut v___y_838_: *mut leanh::LeanObject,
    mut v___y_839_: *mut leanh::LeanObject,
    mut v___y_840_: *mut leanh::LeanObject,
    mut v___y_841_: *mut leanh::LeanObject,
    mut v___y_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_843_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0(
        v_00_u03b1_832_,
        v_msg_833_,
        v___y_834_,
        v___y_835_,
        v___y_836_,
        v___y_837_,
        v___y_838_,
        v___y_839_,
        v___y_840_,
        v___y_841_,
    );
    leanh::lean_dec(v___y_841_);
    leanh::lean_dec_ref(v___y_840_);
    leanh::lean_dec(v___y_839_);
    leanh::lean_dec_ref(v___y_838_);
    leanh::lean_dec(v___y_837_);
    leanh::lean_dec_ref(v___y_836_);
    leanh::lean_dec(v___y_835_);
    leanh::lean_dec_ref(v___y_834_);
    return v_res_843_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1()
-> *mut leanh::LeanObject {
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_859_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__1;
    v___x_860_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___closed__4;
    v___x_861_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSimpArith___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_862_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_858_, v___x_859_, v___x_860_, v___x_861_,
    );
    return v___x_862_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1___boxed(
    mut v_a_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
    return v_res_864_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_873_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__3;
    v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
    return v___x_874_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpArithBang___redArg(
    mut v_stx_875_: *mut leanh::LeanObject,
    mut v_a_876_: *mut leanh::LeanObject,
    mut v_a_877_: *mut leanh::LeanObject,
    mut v_a_878_: *mut leanh::LeanObject,
    mut v_a_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_881_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__0;
    v___x_882_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__2;
    v___x_883_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(
        v_stx_875_, v___x_881_, v___x_882_, v_a_878_, v_a_879_,
    );
    if leanh::lean_obj_tag(v___x_883_) == 0 {
        let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_883_, 1);
        v___x_884_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4_once),
            _init_l_Lean_Elab_Tactic_evalSimpArithBang___redArg___closed__4,
        );
        v___x_885_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(
            v___x_884_, v_a_876_, v_a_877_, v_a_878_, v_a_879_,
        );
        return v___x_885_;
    } else {
        return v___x_883_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpArithBang___redArg___boxed(
    mut v_stx_886_: *mut leanh::LeanObject,
    mut v_a_887_: *mut leanh::LeanObject,
    mut v_a_888_: *mut leanh::LeanObject,
    mut v_a_889_: *mut leanh::LeanObject,
    mut v_a_890_: *mut leanh::LeanObject,
    mut v_a_891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_892_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(
        v_stx_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_,
    );
    leanh::lean_dec(v_a_890_);
    leanh::lean_dec_ref(v_a_889_);
    leanh::lean_dec(v_a_888_);
    leanh::lean_dec_ref(v_a_887_);
    return v_res_892_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpArithBang(
    mut v_stx_893_: *mut leanh::LeanObject,
    mut v_a_894_: *mut leanh::LeanObject,
    mut v_a_895_: *mut leanh::LeanObject,
    mut v_a_896_: *mut leanh::LeanObject,
    mut v_a_897_: *mut leanh::LeanObject,
    mut v_a_898_: *mut leanh::LeanObject,
    mut v_a_899_: *mut leanh::LeanObject,
    mut v_a_900_: *mut leanh::LeanObject,
    mut v_a_901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(
        v_stx_893_, v_a_898_, v_a_899_, v_a_900_, v_a_901_,
    );
    return v___x_903_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpArithBang___boxed(
    mut v_stx_904_: *mut leanh::LeanObject,
    mut v_a_905_: *mut leanh::LeanObject,
    mut v_a_906_: *mut leanh::LeanObject,
    mut v_a_907_: *mut leanh::LeanObject,
    mut v_a_908_: *mut leanh::LeanObject,
    mut v_a_909_: *mut leanh::LeanObject,
    mut v_a_910_: *mut leanh::LeanObject,
    mut v_a_911_: *mut leanh::LeanObject,
    mut v_a_912_: *mut leanh::LeanObject,
    mut v_a_913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_914_ = l_Lean_Elab_Tactic_evalSimpArithBang(
        v_stx_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_,
    );
    leanh::lean_dec(v_a_912_);
    leanh::lean_dec_ref(v_a_911_);
    leanh::lean_dec(v_a_910_);
    leanh::lean_dec_ref(v_a_909_);
    leanh::lean_dec(v_a_908_);
    leanh::lean_dec_ref(v_a_907_);
    leanh::lean_dec(v_a_906_);
    leanh::lean_dec_ref(v_a_905_);
    return v_res_914_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1()
-> *mut leanh::LeanObject {
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_928_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_929_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__1;
    v___x_930_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___closed__3;
    v___x_931_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSimpArithBang___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_932_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_928_, v___x_929_, v___x_930_, v___x_931_,
    );
    return v___x_932_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1___boxed(
    mut v_a_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_934_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
    return v_res_934_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__3;
    v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
    return v___x_944_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllArith___redArg(
    mut v_stx_945_: *mut leanh::LeanObject,
    mut v_a_946_: *mut leanh::LeanObject,
    mut v_a_947_: *mut leanh::LeanObject,
    mut v_a_948_: *mut leanh::LeanObject,
    mut v_a_949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_951_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__0;
    v___x_952_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__2;
    v___x_953_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(
        v_stx_945_, v___x_951_, v___x_952_, v_a_948_, v_a_949_,
    );
    if leanh::lean_obj_tag(v___x_953_) == 0 {
        let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_953_, 1);
        v___x_954_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4_once),
            _init_l_Lean_Elab_Tactic_evalSimpAllArith___redArg___closed__4,
        );
        v___x_955_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(
            v___x_954_, v_a_946_, v_a_947_, v_a_948_, v_a_949_,
        );
        return v___x_955_;
    } else {
        return v___x_953_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllArith___redArg___boxed(
    mut v_stx_956_: *mut leanh::LeanObject,
    mut v_a_957_: *mut leanh::LeanObject,
    mut v_a_958_: *mut leanh::LeanObject,
    mut v_a_959_: *mut leanh::LeanObject,
    mut v_a_960_: *mut leanh::LeanObject,
    mut v_a_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(
        v_stx_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_,
    );
    leanh::lean_dec(v_a_960_);
    leanh::lean_dec_ref(v_a_959_);
    leanh::lean_dec(v_a_958_);
    leanh::lean_dec_ref(v_a_957_);
    return v_res_962_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllArith(
    mut v_stx_963_: *mut leanh::LeanObject,
    mut v_a_964_: *mut leanh::LeanObject,
    mut v_a_965_: *mut leanh::LeanObject,
    mut v_a_966_: *mut leanh::LeanObject,
    mut v_a_967_: *mut leanh::LeanObject,
    mut v_a_968_: *mut leanh::LeanObject,
    mut v_a_969_: *mut leanh::LeanObject,
    mut v_a_970_: *mut leanh::LeanObject,
    mut v_a_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(
        v_stx_963_, v_a_968_, v_a_969_, v_a_970_, v_a_971_,
    );
    return v___x_973_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllArith___boxed(
    mut v_stx_974_: *mut leanh::LeanObject,
    mut v_a_975_: *mut leanh::LeanObject,
    mut v_a_976_: *mut leanh::LeanObject,
    mut v_a_977_: *mut leanh::LeanObject,
    mut v_a_978_: *mut leanh::LeanObject,
    mut v_a_979_: *mut leanh::LeanObject,
    mut v_a_980_: *mut leanh::LeanObject,
    mut v_a_981_: *mut leanh::LeanObject,
    mut v_a_982_: *mut leanh::LeanObject,
    mut v_a_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Lean_Elab_Tactic_evalSimpAllArith(
        v_stx_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_,
    );
    leanh::lean_dec(v_a_982_);
    leanh::lean_dec_ref(v_a_981_);
    leanh::lean_dec(v_a_980_);
    leanh::lean_dec_ref(v_a_979_);
    leanh::lean_dec(v_a_978_);
    leanh::lean_dec_ref(v_a_977_);
    leanh::lean_dec(v_a_976_);
    leanh::lean_dec_ref(v_a_975_);
    return v_res_984_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1()
-> *mut leanh::LeanObject {
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_999_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__1;
    v___x_1000_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___closed__3;
    v___x_1001_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSimpAllArith___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1002_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_998_,
        v___x_999_,
        v___x_1000_,
        v___x_1001_,
    );
    return v___x_1002_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1___boxed(
    mut v_a_1003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1004_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
    return v_res_1004_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1013_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__3;
    v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
    return v___x_1014_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(
    mut v_stx_1015_: *mut leanh::LeanObject,
    mut v_a_1016_: *mut leanh::LeanObject,
    mut v_a_1017_: *mut leanh::LeanObject,
    mut v_a_1018_: *mut leanh::LeanObject,
    mut v_a_1019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__0;
    v___x_1022_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__2;
    v___x_1023_ =
        l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___redArg(
            v_stx_1015_,
            v___x_1021_,
            v___x_1022_,
            v_a_1018_,
            v_a_1019_,
        );
    if leanh::lean_obj_tag(v___x_1023_) == 0 {
        let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_1023_, 1);
        v___x_1024_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4_once
            ),
            _init_l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___closed__4,
        );
        v___x_1025_ = l_Lean_throwError___at___00Lean_Elab_Tactic_evalSimpArith_spec__0___redArg(
            v___x_1024_,
            v_a_1016_,
            v_a_1017_,
            v_a_1018_,
            v_a_1019_,
        );
        return v___x_1025_;
    } else {
        return v___x_1023_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___boxed(
    mut v_stx_1026_: *mut leanh::LeanObject,
    mut v_a_1027_: *mut leanh::LeanObject,
    mut v_a_1028_: *mut leanh::LeanObject,
    mut v_a_1029_: *mut leanh::LeanObject,
    mut v_a_1030_: *mut leanh::LeanObject,
    mut v_a_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1032_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(
        v_stx_1026_,
        v_a_1027_,
        v_a_1028_,
        v_a_1029_,
        v_a_1030_,
    );
    leanh::lean_dec(v_a_1030_);
    leanh::lean_dec_ref(v_a_1029_);
    leanh::lean_dec(v_a_1028_);
    leanh::lean_dec_ref(v_a_1027_);
    return v_res_1032_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllArithBang(
    mut v_stx_1033_: *mut leanh::LeanObject,
    mut v_a_1034_: *mut leanh::LeanObject,
    mut v_a_1035_: *mut leanh::LeanObject,
    mut v_a_1036_: *mut leanh::LeanObject,
    mut v_a_1037_: *mut leanh::LeanObject,
    mut v_a_1038_: *mut leanh::LeanObject,
    mut v_a_1039_: *mut leanh::LeanObject,
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(
        v_stx_1033_,
        v_a_1038_,
        v_a_1039_,
        v_a_1040_,
        v_a_1041_,
    );
    return v___x_1043_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed(
    mut v_stx_1044_: *mut leanh::LeanObject,
    mut v_a_1045_: *mut leanh::LeanObject,
    mut v_a_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
    mut v_a_1048_: *mut leanh::LeanObject,
    mut v_a_1049_: *mut leanh::LeanObject,
    mut v_a_1050_: *mut leanh::LeanObject,
    mut v_a_1051_: *mut leanh::LeanObject,
    mut v_a_1052_: *mut leanh::LeanObject,
    mut v_a_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_Elab_Tactic_evalSimpAllArithBang(
        v_stx_1044_,
        v_a_1045_,
        v_a_1046_,
        v_a_1047_,
        v_a_1048_,
        v_a_1049_,
        v_a_1050_,
        v_a_1051_,
        v_a_1052_,
    );
    leanh::lean_dec(v_a_1052_);
    leanh::lean_dec_ref(v_a_1051_);
    leanh::lean_dec(v_a_1050_);
    leanh::lean_dec_ref(v_a_1049_);
    leanh::lean_dec(v_a_1048_);
    leanh::lean_dec_ref(v_a_1047_);
    leanh::lean_dec(v_a_1046_);
    leanh::lean_dec_ref(v_a_1045_);
    return v_res_1054_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1()
-> *mut leanh::LeanObject {
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1069_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__1;
    v___x_1070_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___closed__3;
    v___x_1071_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1072_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1068_,
        v___x_1069_,
        v___x_1070_,
        v___x_1071_,
    );
    return v___x_1072_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1___boxed(
    mut v_a_1073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
    return v_res_1074_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_SimpArith(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArith___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArith___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_evalSimpAllArithBang___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_SimpArith(
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
pub unsafe fn initialize_Lean_Elab_Tactic_SimpArith(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_SimpArith(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_SimpArith(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_SimpArith(builtin);
}