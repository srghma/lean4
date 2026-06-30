// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Delta
// Imports: Lean.Elab.Tactic.Delta Lean.Elab.Tactic.Conv.Basic
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_name_eq,
    lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_changeLhs,
    l_Lean_Elab_Tactic_Conv_getLhs___redArg, runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Delta::{
    initialize_Lean_Elab_Tactic_Delta, runtime_initialize_Lean_Elab_Tactic_Delta,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_hasMVar;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Tactic::Delta::l_Lean_Meta_deltaExpand;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 108, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3_value) as *mut leanh::LeanObject,2622230176999461939 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__4_value) as *mut leanh::LeanObject,8745909130110294463 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__7_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 68, 101, 108, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__6_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__7_value) as *mut leanh::LeanObject,13357704951301403385 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 16 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 18 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 18 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 61 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 61 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(
    mut v_e_295_: *mut leanh::LeanObject,
    mut v___y_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_298_: u8 = 0;
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_312_: u8 = 0;
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_318_: u8 = 0;
    let mut v_unused_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_298_ = l_Lean_Expr_hasMVar(v_e_295_);
                if v___x_298_ == 0 {
                    v___x_299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_299_, 0, v_e_295_);
                    return v___x_299_;
                } else {
                    v___x_300_ = lean_st_ref_get(v___y_296_);
                    v_mctx_301_ = leanh::lean_ctor_get(v___x_300_, 0);
                    leanh::lean_inc_ref(v_mctx_301_);
                    leanh::lean_dec(v___x_300_);
                    v___x_302_ = l_Lean_instantiateMVarsCore(v_mctx_301_, v_e_295_);
                    v_fst_303_ = leanh::lean_ctor_get(v___x_302_, 0);
                    leanh::lean_inc(v_fst_303_);
                    v_snd_304_ = leanh::lean_ctor_get(v___x_302_, 1);
                    leanh::lean_inc(v_snd_304_);
                    leanh::lean_dec_ref(v___x_302_);
                    v___x_305_ = lean_st_ref_take(v___y_296_);
                    v_cache_306_ = leanh::lean_ctor_get(v___x_305_, 1);
                    v_zetaDeltaFVarIds_307_ = leanh::lean_ctor_get(v___x_305_, 2);
                    v_postponed_308_ = leanh::lean_ctor_get(v___x_305_, 3);
                    v_diag_309_ = leanh::lean_ctor_get(v___x_305_, 4);
                    v_isSharedCheck_318_ = (!leanh::lean_is_exclusive(v___x_305_)) as u8;
                    if v_isSharedCheck_318_ == 0 {
                        v_unused_319_ = leanh::lean_ctor_get(v___x_305_, 0);
                        leanh::lean_dec(v_unused_319_);
                        v___x_311_ = v___x_305_;
                        v_isShared_312_ = v_isSharedCheck_318_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_309_);
                        leanh::lean_inc(v_postponed_308_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_307_);
                        leanh::lean_inc(v_cache_306_);
                        leanh::lean_dec(v___x_305_);
                        v___x_311_ = leanh::lean_box(0);
                        v_isShared_312_ = v_isSharedCheck_318_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_312_ == 0 {
                    leanh::lean_ctor_set(v___x_311_, 0, v_snd_304_);
                    v___x_314_ = v___x_311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_317_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_317_, 0, v_snd_304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_317_, 1, v_cache_306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_317_, 2, v_zetaDeltaFVarIds_307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_317_, 3, v_postponed_308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_317_, 4, v_diag_309_);
                    v___x_314_ = v_reuseFailAlloc_317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_315_ = lean_st_ref_set(v___y_296_, v___x_314_);
                v___x_316_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_316_, 0, v_fst_303_);
                return v___x_316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg___boxed(
    mut v_e_320_: *mut leanh::LeanObject,
    mut v___y_321_: *mut leanh::LeanObject,
    mut v___y_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_323_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(
        v_e_320_, v___y_321_,
    );
    leanh::lean_dec(v___y_321_);
    return v_res_323_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1(
    mut v_e_324_: *mut leanh::LeanObject,
    mut v___y_325_: *mut leanh::LeanObject,
    mut v___y_326_: *mut leanh::LeanObject,
    mut v___y_327_: *mut leanh::LeanObject,
    mut v___y_328_: *mut leanh::LeanObject,
    mut v___y_329_: *mut leanh::LeanObject,
    mut v___y_330_: *mut leanh::LeanObject,
    mut v___y_331_: *mut leanh::LeanObject,
    mut v___y_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(
        v_e_324_, v___y_330_,
    );
    return v___x_334_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___boxed(
    mut v_e_335_: *mut leanh::LeanObject,
    mut v___y_336_: *mut leanh::LeanObject,
    mut v___y_337_: *mut leanh::LeanObject,
    mut v___y_338_: *mut leanh::LeanObject,
    mut v___y_339_: *mut leanh::LeanObject,
    mut v___y_340_: *mut leanh::LeanObject,
    mut v___y_341_: *mut leanh::LeanObject,
    mut v___y_342_: *mut leanh::LeanObject,
    mut v___y_343_: *mut leanh::LeanObject,
    mut v___y_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1(
        v_e_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_,
        v___y_342_, v___y_343_,
    );
    leanh::lean_dec(v___y_343_);
    leanh::lean_dec_ref(v___y_342_);
    leanh::lean_dec(v___y_341_);
    leanh::lean_dec_ref(v___y_340_);
    leanh::lean_dec(v___y_339_);
    leanh::lean_dec_ref(v___y_338_);
    leanh::lean_dec(v___y_337_);
    leanh::lean_dec_ref(v___y_336_);
    return v_res_345_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(
    mut v_a_346_: *mut leanh::LeanObject,
    mut v_as_347_: *mut leanh::LeanObject,
    mut v_i_348_: usize,
    mut v_stop_349_: usize,
) -> u8 {
    let mut v___x_350_: u8 = 0;
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: u8 = 0;
    let mut v___x_353_: usize = 0;
    let mut v___x_354_: usize = 0;
    let mut v___x_356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_350_ = lean_usize_dec_eq(v_i_348_, v_stop_349_);
                if v___x_350_ == 0 {
                    v___x_351_ = lean_array_uget_borrowed(v_as_347_, v_i_348_);
                    v___x_352_ = lean_name_eq(v_a_346_, v___x_351_);
                    if v___x_352_ == 0 {
                        v___x_353_ = 1usize;
                        v___x_354_ = lean_usize_add(v_i_348_, v___x_353_);
                        v_i_348_ = v___x_354_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_352_;
                    }
                } else {
                    v___x_356_ = 0;
                    return v___x_356_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2___boxed(
    mut v_a_357_: *mut leanh::LeanObject,
    mut v_as_358_: *mut leanh::LeanObject,
    mut v_i_359_: *mut leanh::LeanObject,
    mut v_stop_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_361_: usize = 0;
    let mut v_stop_boxed_362_: usize = 0;
    let mut v_res_363_: u8 = 0;
    let mut v_r_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_361_ = leanh::lean_unbox_usize(v_i_359_);
    leanh::lean_dec(v_i_359_);
    v_stop_boxed_362_ = leanh::lean_unbox_usize(v_stop_360_);
    leanh::lean_dec(v_stop_360_);
    v_res_363_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(v_a_357_, v_as_358_, v_i_boxed_361_, v_stop_boxed_362_);
    leanh::lean_dec_ref(v_as_358_);
    leanh::lean_dec(v_a_357_);
    v_r_364_ = leanh::lean_box((v_res_363_) as usize);
    return v_r_364_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(
    mut v_as_365_: *mut leanh::LeanObject,
    mut v_a_366_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: u8 = 0;
    v___x_367_ = leanh::lean_unsigned_to_nat(0);
    v___x_368_ = lean_array_get_size(v_as_365_);
    v___x_369_ = lean_nat_dec_lt(v___x_367_, v___x_368_);
    if v___x_369_ == 0 {
        return v___x_369_;
    } else {
        if v___x_369_ == 0 {
            return v___x_369_;
        } else {
            let mut v___x_370_: usize = 0;
            let mut v___x_371_: usize = 0;
            let mut v___x_372_: u8 = 0;
            v___x_370_ = 0usize;
            v___x_371_ = lean_usize_of_nat(v___x_368_);
            v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2_spec__2(v_a_366_, v_as_365_, v___x_370_, v___x_371_);
            return v___x_372_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2___boxed(
    mut v_as_373_: *mut leanh::LeanObject,
    mut v_a_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_375_: u8 = 0;
    let mut v_r_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_375_ =
        l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(v_as_373_, v_a_374_);
    leanh::lean_dec(v_a_374_);
    leanh::lean_dec_ref(v_as_373_);
    v_r_376_ = leanh::lean_box((v_res_375_) as usize);
    return v_r_376_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDelta___lam__0(
    mut v_a_377_: *mut leanh::LeanObject,
    mut v___y_378_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_379_: u8 = 0;
    v___x_379_ =
        l_Array_contains___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__2(v_a_377_, v___y_378_);
    return v___x_379_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDelta___lam__0___boxed(
    mut v_a_380_: *mut leanh::LeanObject,
    mut v___y_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_382_: u8 = 0;
    let mut v_r_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_382_ = l_Lean_Elab_Tactic_Conv_evalDelta___lam__0(v_a_380_, v___y_381_);
    leanh::lean_dec(v___y_381_);
    leanh::lean_dec_ref(v_a_380_);
    v_r_383_ = leanh::lean_box((v_res_382_) as usize);
    return v_r_383_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(
    mut v_sz_384_: usize,
    mut v_i_385_: usize,
    mut v_bs_386_: *mut leanh::LeanObject,
    mut v___y_387_: *mut leanh::LeanObject,
    mut v___y_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: u8 = 0;
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: usize = 0;
    let mut v___x_399_: usize = 0;
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_405_: u8 = 0;
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_390_ = lean_usize_dec_lt(v_i_385_, v_sz_384_);
                if v___x_390_ == 0 {
                    v___x_391_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_391_, 0, v_bs_386_);
                    return v___x_391_;
                } else {
                    v_v_392_ = lean_array_uget_borrowed(v_bs_386_, v_i_385_);
                    v___x_393_ = leanh::lean_box(0);
                    leanh::lean_inc(v_v_392_);
                    v___x_394_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_v_392_, v___x_393_, v___y_387_, v___y_388_,
                    );
                    if leanh::lean_obj_tag(v___x_394_) == 0 {
                        v_a_395_ = leanh::lean_ctor_get(v___x_394_, 0);
                        leanh::lean_inc(v_a_395_);
                        leanh::lean_dec_ref_known(v___x_394_, 1);
                        v___x_396_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_397_ = lean_array_uset(v_bs_386_, v_i_385_, v___x_396_);
                        v___x_398_ = 1usize;
                        v___x_399_ = lean_usize_add(v_i_385_, v___x_398_);
                        v___x_400_ = lean_array_uset(v_bs_x27_397_, v_i_385_, v_a_395_);
                        v_i_385_ = v___x_399_;
                        v_bs_386_ = v___x_400_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_386_);
                        v_a_402_ = leanh::lean_ctor_get(v___x_394_, 0);
                        v_isSharedCheck_409_ = (!leanh::lean_is_exclusive(v___x_394_)) as u8;
                        if v_isSharedCheck_409_ == 0 {
                            v___x_404_ = v___x_394_;
                            v_isShared_405_ = v_isSharedCheck_409_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_402_);
                            leanh::lean_dec(v___x_394_);
                            v___x_404_ = leanh::lean_box(0);
                            v_isShared_405_ = v_isSharedCheck_409_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_405_ == 0 {
                    v___x_407_ = v___x_404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_408_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
                    v___x_407_ = v_reuseFailAlloc_408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_407_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg___boxed(
    mut v_sz_410_: *mut leanh::LeanObject,
    mut v_i_411_: *mut leanh::LeanObject,
    mut v_bs_412_: *mut leanh::LeanObject,
    mut v___y_413_: *mut leanh::LeanObject,
    mut v___y_414_: *mut leanh::LeanObject,
    mut v___y_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_416_: usize = 0;
    let mut v_i_boxed_417_: usize = 0;
    let mut v_res_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_416_ = leanh::lean_unbox_usize(v_sz_410_);
    leanh::lean_dec(v_sz_410_);
    v_i_boxed_417_ = leanh::lean_unbox_usize(v_i_411_);
    leanh::lean_dec(v_i_411_);
    v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_boxed_416_, v_i_boxed_417_, v_bs_412_, v___y_413_, v___y_414_);
    leanh::lean_dec(v___y_414_);
    leanh::lean_dec_ref(v___y_413_);
    return v_res_418_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDelta___lam__1(
    mut v___x_419_: *mut leanh::LeanObject,
    mut v___y_420_: *mut leanh::LeanObject,
    mut v___y_421_: *mut leanh::LeanObject,
    mut v___y_422_: *mut leanh::LeanObject,
    mut v___y_423_: *mut leanh::LeanObject,
    mut v___y_424_: *mut leanh::LeanObject,
    mut v___y_425_: *mut leanh::LeanObject,
    mut v___y_426_: *mut leanh::LeanObject,
    mut v___y_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_429_: usize = 0;
    let mut v___x_430_: usize = 0;
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: u8 = 0;
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_449_: u8 = 0;
    let mut v_a_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_453_: u8 = 0;
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_457_: u8 = 0;
    let mut v_a_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_461_: u8 = 0;
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_429_ = lean_array_size(v___x_419_);
                v___x_430_ = 0usize;
                v___x_431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_429_, v___x_430_, v___x_419_, v___y_426_, v___y_427_);
                if leanh::lean_obj_tag(v___x_431_) == 0 {
                    v_a_432_ = leanh::lean_ctor_get(v___x_431_, 0);
                    leanh::lean_inc(v_a_432_);
                    leanh::lean_dec_ref_known(v___x_431_, 1);
                    v___x_433_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_421_, v___y_424_, v___y_425_, v___y_426_, v___y_427_,
                    );
                    if leanh::lean_obj_tag(v___x_433_) == 0 {
                        v_a_434_ = leanh::lean_ctor_get(v___x_433_, 0);
                        leanh::lean_inc(v_a_434_);
                        leanh::lean_dec_ref_known(v___x_433_, 1);
                        v___x_435_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__1___redArg(v_a_434_, v___y_425_);
                        v_a_436_ = leanh::lean_ctor_get(v___x_435_, 0);
                        leanh::lean_inc(v_a_436_);
                        leanh::lean_dec_ref(v___x_435_);
                        v___f_437_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalDelta___lam__0___boxed
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_437_, 0, v_a_432_);
                        v___x_438_ = 0;
                        v___x_439_ = l_Lean_Meta_deltaExpand(
                            v_a_436_, v___f_437_, v___x_438_, v___y_426_, v___y_427_,
                        );
                        if leanh::lean_obj_tag(v___x_439_) == 0 {
                            v_a_440_ = leanh::lean_ctor_get(v___x_439_, 0);
                            leanh::lean_inc(v_a_440_);
                            leanh::lean_dec_ref_known(v___x_439_, 1);
                            v___x_441_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_a_440_, v___y_420_, v___y_421_, v___y_422_, v___y_423_,
                                v___y_424_, v___y_425_, v___y_426_, v___y_427_,
                            );
                            return v___x_441_;
                        } else {
                            v_a_442_ = leanh::lean_ctor_get(v___x_439_, 0);
                            v_isSharedCheck_449_ =
                                (!leanh::lean_is_exclusive(v___x_439_)) as u8;
                            if v_isSharedCheck_449_ == 0 {
                                v___x_444_ = v___x_439_;
                                v_isShared_445_ = v_isSharedCheck_449_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_442_);
                                leanh::lean_dec(v___x_439_);
                                v___x_444_ = leanh::lean_box(0);
                                v_isShared_445_ = v_isSharedCheck_449_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_432_);
                        v_a_450_ = leanh::lean_ctor_get(v___x_433_, 0);
                        v_isSharedCheck_457_ = (!leanh::lean_is_exclusive(v___x_433_)) as u8;
                        if v_isSharedCheck_457_ == 0 {
                            v___x_452_ = v___x_433_;
                            v_isShared_453_ = v_isSharedCheck_457_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_450_);
                            leanh::lean_dec(v___x_433_);
                            v___x_452_ = leanh::lean_box(0);
                            v_isShared_453_ = v_isSharedCheck_457_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_458_ = leanh::lean_ctor_get(v___x_431_, 0);
                    v_isSharedCheck_465_ = (!leanh::lean_is_exclusive(v___x_431_)) as u8;
                    if v_isSharedCheck_465_ == 0 {
                        v___x_460_ = v___x_431_;
                        v_isShared_461_ = v_isSharedCheck_465_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_458_);
                        leanh::lean_dec(v___x_431_);
                        v___x_460_ = leanh::lean_box(0);
                        v_isShared_461_ = v_isSharedCheck_465_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_445_ == 0 {
                    v___x_447_ = v___x_444_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
                    v___x_447_ = v_reuseFailAlloc_448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_447_;
            }
            3 => {
                if v_isShared_453_ == 0 {
                    v___x_455_ = v___x_452_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
                    v___x_455_ = v_reuseFailAlloc_456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_455_;
            }
            5 => {
                if v_isShared_461_ == 0 {
                    v___x_463_ = v___x_460_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_464_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
                    v___x_463_ = v_reuseFailAlloc_464_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDelta___lam__1___boxed(
    mut v___x_466_: *mut leanh::LeanObject,
    mut v___y_467_: *mut leanh::LeanObject,
    mut v___y_468_: *mut leanh::LeanObject,
    mut v___y_469_: *mut leanh::LeanObject,
    mut v___y_470_: *mut leanh::LeanObject,
    mut v___y_471_: *mut leanh::LeanObject,
    mut v___y_472_: *mut leanh::LeanObject,
    mut v___y_473_: *mut leanh::LeanObject,
    mut v___y_474_: *mut leanh::LeanObject,
    mut v___y_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Lean_Elab_Tactic_Conv_evalDelta___lam__1(
        v___x_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_,
        v___y_473_, v___y_474_,
    );
    leanh::lean_dec(v___y_474_);
    leanh::lean_dec_ref(v___y_473_);
    leanh::lean_dec(v___y_472_);
    leanh::lean_dec_ref(v___y_471_);
    leanh::lean_dec(v___y_470_);
    leanh::lean_dec_ref(v___y_469_);
    leanh::lean_dec(v___y_468_);
    leanh::lean_dec_ref(v___y_467_);
    return v_res_476_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDelta(
    mut v_stx_477_: *mut leanh::LeanObject,
    mut v_a_478_: *mut leanh::LeanObject,
    mut v_a_479_: *mut leanh::LeanObject,
    mut v_a_480_: *mut leanh::LeanObject,
    mut v_a_481_: *mut leanh::LeanObject,
    mut v_a_482_: *mut leanh::LeanObject,
    mut v_a_483_: *mut leanh::LeanObject,
    mut v_a_484_: *mut leanh::LeanObject,
    mut v_a_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = leanh::lean_unsigned_to_nat(1);
    v___x_488_ = l_Lean_Syntax_getArg(v_stx_477_, v___x_487_);
    v___x_489_ = l_Lean_Syntax_getArgs(v___x_488_);
    leanh::lean_dec(v___x_488_);
    v___f_490_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDelta___lam__1___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    leanh::lean_closure_set(v___f_490_, 0, v___x_489_);
    v___x_491_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_490_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_,
    );
    return v___x_491_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDelta___boxed(
    mut v_stx_492_: *mut leanh::LeanObject,
    mut v_a_493_: *mut leanh::LeanObject,
    mut v_a_494_: *mut leanh::LeanObject,
    mut v_a_495_: *mut leanh::LeanObject,
    mut v_a_496_: *mut leanh::LeanObject,
    mut v_a_497_: *mut leanh::LeanObject,
    mut v_a_498_: *mut leanh::LeanObject,
    mut v_a_499_: *mut leanh::LeanObject,
    mut v_a_500_: *mut leanh::LeanObject,
    mut v_a_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_Lean_Elab_Tactic_Conv_evalDelta(
        v_stx_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_,
    );
    leanh::lean_dec(v_a_500_);
    leanh::lean_dec_ref(v_a_499_);
    leanh::lean_dec(v_a_498_);
    leanh::lean_dec_ref(v_a_497_);
    leanh::lean_dec(v_a_496_);
    leanh::lean_dec_ref(v_a_495_);
    leanh::lean_dec(v_a_494_);
    leanh::lean_dec_ref(v_a_493_);
    leanh::lean_dec(v_stx_492_);
    return v_res_502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0(
    mut v_sz_503_: usize,
    mut v_i_504_: usize,
    mut v_bs_505_: *mut leanh::LeanObject,
    mut v___y_506_: *mut leanh::LeanObject,
    mut v___y_507_: *mut leanh::LeanObject,
    mut v___y_508_: *mut leanh::LeanObject,
    mut v___y_509_: *mut leanh::LeanObject,
    mut v___y_510_: *mut leanh::LeanObject,
    mut v___y_511_: *mut leanh::LeanObject,
    mut v___y_512_: *mut leanh::LeanObject,
    mut v___y_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___redArg(v_sz_503_, v_i_504_, v_bs_505_, v___y_512_, v___y_513_);
    return v___x_515_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0___boxed(
    mut v_sz_516_: *mut leanh::LeanObject,
    mut v_i_517_: *mut leanh::LeanObject,
    mut v_bs_518_: *mut leanh::LeanObject,
    mut v___y_519_: *mut leanh::LeanObject,
    mut v___y_520_: *mut leanh::LeanObject,
    mut v___y_521_: *mut leanh::LeanObject,
    mut v___y_522_: *mut leanh::LeanObject,
    mut v___y_523_: *mut leanh::LeanObject,
    mut v___y_524_: *mut leanh::LeanObject,
    mut v___y_525_: *mut leanh::LeanObject,
    mut v___y_526_: *mut leanh::LeanObject,
    mut v___y_527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_528_: usize = 0;
    let mut v_i_boxed_529_: usize = 0;
    let mut v_res_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_528_ = leanh::lean_unbox_usize(v_sz_516_);
    leanh::lean_dec(v_sz_516_);
    v_i_boxed_529_ = leanh::lean_unbox_usize(v_i_517_);
    leanh::lean_dec(v_i_517_);
    v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalDelta_spec__0(v_sz_boxed_528_, v_i_boxed_529_, v_bs_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
    leanh::lean_dec(v___y_526_);
    leanh::lean_dec_ref(v___y_525_);
    leanh::lean_dec(v___y_524_);
    leanh::lean_dec_ref(v___y_523_);
    leanh::lean_dec(v___y_522_);
    leanh::lean_dec_ref(v___y_521_);
    leanh::lean_dec(v___y_520_);
    leanh::lean_dec_ref(v___y_519_);
    return v_res_530_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1()
-> *mut leanh::LeanObject {
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_552_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__5;
    v___x_553_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8;
    v___x_554_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDelta___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_555_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_551_, v___x_552_, v___x_553_, v___x_554_,
    );
    return v___x_555_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___boxed(
    mut v_a_556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_557_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1();
    return v_res_557_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1___closed__8;
    v___x_585_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___closed__6;
    v___x_586_ = l_Lean_addBuiltinDeclarationRanges(v___x_584_, v___x_585_);
    return v___x_586_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3___boxed(
    mut v_a_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_588_ = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3();
    return v_res_588_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Delta(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Delta_0__Lean_Elab_Tactic_Conv_evalDelta___regBuiltin_Lean_Elab_Tactic_Conv_evalDelta_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Delta(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Delta(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Delta(builtin);
}