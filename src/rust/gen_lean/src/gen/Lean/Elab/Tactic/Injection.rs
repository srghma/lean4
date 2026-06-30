// Lean compiler output
// Module: Lean.Elab.Tactic.Injection
// Imports: Lean.Meta.Tactic.Injection Lean.Meta.Tactic.Assumption Lean.Elab.Tactic.ElabTerm
use crate::ffi::lean_array_to_list;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_getNameOfIdent_x27,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_elabAsFVar,
    runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::Assumption::{
    initialize_Lean_Meta_Tactic_Assumption, l_Lean_MVarId_assumptionCore,
    runtime_initialize_Lean_Meta_Tactic_Assumption,
};
use crate::r#gen::Lean::Meta::Tactic::Injection::{
    initialize_Lean_Meta_Tactic_Injection, l_Lean_Meta_injection, l_Lean_Meta_injections,
    runtime_initialize_Lean_Meta_Tactic_Injection,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_throwTacticEx___redArg;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [116, 111, 111, 32, 109, 97, 110, 121, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 32, 112, 114, 111, 118, 105, 100, 101, 100, 44, 32, 117, 110, 117, 115, 101, 100, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value:
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
    m_data: [105, 110, 106, 101, 99, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        12874249535713742015 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value) as *mut leanh::LeanObject,8171666429901634422 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 73, 110, 106, 101, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value) as *mut leanh::LeanObject,6549291366557724274 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 37 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 103 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 103 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 106, 101, 99, 116, 105, 111, 110, 115, 0],
};
static mut l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        5163565424560827901 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value) as *mut leanh::LeanObject,12924360897913574244 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 73, 110, 106, 101, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value) as *mut leanh::LeanObject,15701361205147766637 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 102 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 102 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 49 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(
    mut v_a_430_: *mut leanh::LeanObject,
    mut v_a_431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_437_: u8 = 0;
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_430_) == 0 {
                    v___x_432_ = l_List_reverse___redArg(v_a_431_);
                    return v___x_432_;
                } else {
                    v_head_433_ = leanh::lean_ctor_get(v_a_430_, 0);
                    v_tail_434_ = leanh::lean_ctor_get(v_a_430_, 1);
                    v_isSharedCheck_443_ = (!leanh::lean_is_exclusive(v_a_430_)) as u8;
                    if v_isSharedCheck_443_ == 0 {
                        v___x_436_ = v_a_430_;
                        v_isShared_437_ = v_isSharedCheck_443_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_434_);
                        leanh::lean_inc(v_head_433_);
                        leanh::lean_dec(v_a_430_);
                        v___x_436_ = leanh::lean_box(0);
                        v_isShared_437_ = v_isSharedCheck_443_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_438_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_head_433_);
                leanh::lean_dec(v_head_433_);
                if v_isShared_437_ == 0 {
                    leanh::lean_ctor_set(v___x_436_, 1, v_a_431_);
                    leanh::lean_ctor_set(v___x_436_, 0, v___x_438_);
                    v___x_440_ = v___x_436_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_442_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_442_, 1, v_a_431_);
                    v___x_440_ = v_reuseFailAlloc_442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_430_ = v_tail_434_;
                v_a_431_ = v___x_440_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(
    mut v_stx_444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_445_: u8 = 0;
    v___x_445_ = l_Lean_Syntax_isNone(v_stx_444_);
    if v___x_445_ == 0 {
        let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_446_ = leanh::lean_unsigned_to_nat(1);
        v___x_447_ = l_Lean_Syntax_getArg(v_stx_444_, v___x_446_);
        v___x_448_ = l_Lean_Syntax_getArgs(v___x_447_);
        leanh::lean_dec(v___x_447_);
        v___x_449_ = lean_array_to_list(v___x_448_);
        v___x_450_ = leanh::lean_box(0);
        v___x_451_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(v___x_449_, v___x_450_);
        return v___x_451_;
    } else {
        let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_452_ = leanh::lean_box(0);
        return v___x_452_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds___boxed(
    mut v_stx_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_454_ =
        l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(v_stx_453_);
    leanh::lean_dec(v_stx_453_);
    return v_res_454_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(
    mut v_a_455_: *mut leanh::LeanObject,
    mut v_a_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_462_: u8 = 0;
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_455_) == 0 {
                    v___x_457_ = l_List_reverse___redArg(v_a_456_);
                    return v___x_457_;
                } else {
                    v_head_458_ = leanh::lean_ctor_get(v_a_455_, 0);
                    v_tail_459_ = leanh::lean_ctor_get(v_a_455_, 1);
                    v_isSharedCheck_468_ = (!leanh::lean_is_exclusive(v_a_455_)) as u8;
                    if v_isSharedCheck_468_ == 0 {
                        v___x_461_ = v_a_455_;
                        v_isShared_462_ = v_isSharedCheck_468_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_459_);
                        leanh::lean_inc(v_head_458_);
                        leanh::lean_dec(v_a_455_);
                        v___x_461_ = leanh::lean_box(0);
                        v_isShared_462_ = v_isSharedCheck_468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_463_ = l_Lean_MessageData_ofName(v_head_458_);
                if v_isShared_462_ == 0 {
                    leanh::lean_ctor_set(v___x_461_, 1, v_a_456_);
                    leanh::lean_ctor_set(v___x_461_, 0, v___x_463_);
                    v___x_465_ = v___x_461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_467_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_467_, 1, v_a_456_);
                    v___x_465_ = v_reuseFailAlloc_467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_455_ = v_tail_459_;
                v_a_456_ = v___x_465_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_470_ =
        l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0;
    v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
    return v___x_471_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(
    mut v_tacticName_472_: *mut leanh::LeanObject,
    mut v_mvarId_473_: *mut leanh::LeanObject,
    mut v_unusedIds_474_: *mut leanh::LeanObject,
    mut v_a_475_: *mut leanh::LeanObject,
    mut v_a_476_: *mut leanh::LeanObject,
    mut v_a_477_: *mut leanh::LeanObject,
    mut v_a_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_480_: u8 = 0;
    v___x_480_ = l_List_isEmpty___redArg(v_unusedIds_474_);
    if v___x_480_ == 0 {
        let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1_once), _init_l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1);
        v___x_482_ = leanh::lean_box(0);
        v___x_483_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(v_unusedIds_474_, v___x_482_);
        v___x_484_ = l_Lean_MessageData_ofList(v___x_483_);
        v___x_485_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_485_, 0, v___x_481_);
        leanh::lean_ctor_set(v___x_485_, 1, v___x_484_);
        v___x_486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_486_, 0, v___x_485_);
        v___x_487_ = l_Lean_Meta_throwTacticEx___redArg(
            v_tacticName_472_,
            v_mvarId_473_,
            v___x_486_,
            v_a_475_,
            v_a_476_,
            v_a_477_,
            v_a_478_,
        );
        return v___x_487_;
    } else {
        let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_unusedIds_474_);
        leanh::lean_dec(v_mvarId_473_);
        leanh::lean_dec(v_tacticName_472_);
        v___x_488_ = leanh::lean_box(0);
        v___x_489_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_489_, 0, v___x_488_);
        return v___x_489_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___boxed(
    mut v_tacticName_490_: *mut leanh::LeanObject,
    mut v_mvarId_491_: *mut leanh::LeanObject,
    mut v_unusedIds_492_: *mut leanh::LeanObject,
    mut v_a_493_: *mut leanh::LeanObject,
    mut v_a_494_: *mut leanh::LeanObject,
    mut v_a_495_: *mut leanh::LeanObject,
    mut v_a_496_: *mut leanh::LeanObject,
    mut v_a_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_498_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(
        v_tacticName_490_,
        v_mvarId_491_,
        v_unusedIds_492_,
        v_a_493_,
        v_a_494_,
        v_a_495_,
        v_a_496_,
    );
    leanh::lean_dec(v_a_496_);
    leanh::lean_dec_ref(v_a_495_);
    leanh::lean_dec(v_a_494_);
    leanh::lean_dec_ref(v_a_493_);
    return v_res_498_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(
    mut v_mvarId_499_: *mut leanh::LeanObject,
    mut v_a_500_: *mut leanh::LeanObject,
    mut v_a_501_: *mut leanh::LeanObject,
    mut v_a_502_: *mut leanh::LeanObject,
    mut v_a_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_509_: u8 = 0;
    let mut v___x_510_: u8 = 0;
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_520_: u8 = 0;
    let mut v_a_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_524_: u8 = 0;
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_499_);
                v___x_505_ = l_Lean_MVarId_assumptionCore(
                    v_mvarId_499_,
                    v_a_500_,
                    v_a_501_,
                    v_a_502_,
                    v_a_503_,
                );
                if leanh::lean_obj_tag(v___x_505_) == 0 {
                    v_a_506_ = leanh::lean_ctor_get(v___x_505_, 0);
                    v_isSharedCheck_520_ = (!leanh::lean_is_exclusive(v___x_505_)) as u8;
                    if v_isSharedCheck_520_ == 0 {
                        v___x_508_ = v___x_505_;
                        v_isShared_509_ = v_isSharedCheck_520_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_506_);
                        leanh::lean_dec(v___x_505_);
                        v___x_508_ = leanh::lean_box(0);
                        v_isShared_509_ = v_isSharedCheck_520_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_499_);
                    v_a_521_ = leanh::lean_ctor_get(v___x_505_, 0);
                    v_isSharedCheck_528_ = (!leanh::lean_is_exclusive(v___x_505_)) as u8;
                    if v_isSharedCheck_528_ == 0 {
                        v___x_523_ = v___x_505_;
                        v_isShared_524_ = v_isSharedCheck_528_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_521_);
                        leanh::lean_dec(v___x_505_);
                        v___x_523_ = leanh::lean_box(0);
                        v_isShared_524_ = v_isSharedCheck_528_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_510_ = (leanh::lean_unbox(v_a_506_) as u8);
                leanh::lean_dec(v_a_506_);
                if v___x_510_ == 0 {
                    v___x_511_ = leanh::lean_box(0);
                    v___x_512_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_512_, 0, v_mvarId_499_);
                    leanh::lean_ctor_set(v___x_512_, 1, v___x_511_);
                    if v_isShared_509_ == 0 {
                        leanh::lean_ctor_set(v___x_508_, 0, v___x_512_);
                        v___x_514_ = v___x_508_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
                        v___x_514_ = v_reuseFailAlloc_515_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_499_);
                    v___x_516_ = leanh::lean_box(0);
                    if v_isShared_509_ == 0 {
                        leanh::lean_ctor_set(v___x_508_, 0, v___x_516_);
                        v___x_518_ = v___x_508_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
                        v___x_518_ = v_reuseFailAlloc_519_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_514_;
            }
            3 => {
                return v___x_518_;
            }
            4 => {
                if v_isShared_524_ == 0 {
                    v___x_526_ = v___x_523_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
                    v___x_526_ = v_reuseFailAlloc_527_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption___boxed(
    mut v_mvarId_529_: *mut leanh::LeanObject,
    mut v_a_530_: *mut leanh::LeanObject,
    mut v_a_531_: *mut leanh::LeanObject,
    mut v_a_532_: *mut leanh::LeanObject,
    mut v_a_533_: *mut leanh::LeanObject,
    mut v_a_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(
        v_mvarId_529_,
        v_a_530_,
        v_a_531_,
        v_a_532_,
        v_a_533_,
    );
    leanh::lean_dec(v_a_533_);
    leanh::lean_dec_ref(v_a_532_);
    leanh::lean_dec(v_a_531_);
    leanh::lean_dec_ref(v_a_530_);
    return v_res_535_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjection___lam__0(
    mut v_a_539_: *mut leanh::LeanObject,
    mut v___x_540_: *mut leanh::LeanObject,
    mut v___y_541_: *mut leanh::LeanObject,
    mut v___y_542_: *mut leanh::LeanObject,
    mut v___y_543_: *mut leanh::LeanObject,
    mut v___y_544_: *mut leanh::LeanObject,
    mut v___y_545_: *mut leanh::LeanObject,
    mut v___y_546_: *mut leanh::LeanObject,
    mut v___y_547_: *mut leanh::LeanObject,
    mut v___y_548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_555_: u8 = 0;
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_560_: u8 = 0;
    let mut v_unused_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remainingNames_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_578_: u8 = 0;
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_582_: u8 = 0;
    let mut v_a_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_586_: u8 = 0;
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v_a_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_562_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_542_, v___y_545_, v___y_546_, v___y_547_, v___y_548_,
                );
                if leanh::lean_obj_tag(v___x_562_) == 0 {
                    v_a_563_ = leanh::lean_ctor_get(v___x_562_, 0);
                    leanh::lean_inc_n(v_a_563_, 2);
                    leanh::lean_dec_ref_known(v___x_562_, 1);
                    leanh::lean_inc(v___x_540_);
                    v___x_564_ = l_Lean_Meta_injection(
                        v_a_563_, v_a_539_, v___x_540_, v___y_545_, v___y_546_, v___y_547_,
                        v___y_548_,
                    );
                    if leanh::lean_obj_tag(v___x_564_) == 0 {
                        v_a_565_ = leanh::lean_ctor_get(v___x_564_, 0);
                        leanh::lean_inc(v_a_565_);
                        leanh::lean_dec_ref_known(v___x_564_, 1);
                        if leanh::lean_obj_tag(v_a_565_) == 0 {
                            v___x_566_ = l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1;
                            v___x_567_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_566_, v_a_563_, v___x_540_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
                            if leanh::lean_obj_tag(v___x_567_) == 0 {
                                leanh::lean_dec_ref_known(v___x_567_, 1);
                                v___x_568_ = leanh::lean_box(0);
                                v_a_551_ = v___x_568_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_567_;
                            }
                        } else {
                            leanh::lean_dec(v___x_540_);
                            v_mvarId_569_ = leanh::lean_ctor_get(v_a_565_, 0);
                            leanh::lean_inc(v_mvarId_569_);
                            v_remainingNames_570_ = leanh::lean_ctor_get(v_a_565_, 2);
                            leanh::lean_inc(v_remainingNames_570_);
                            leanh::lean_dec_ref_known(v_a_565_, 3);
                            v___x_571_ = l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1;
                            v___x_572_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_571_, v_a_563_, v_remainingNames_570_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
                            if leanh::lean_obj_tag(v___x_572_) == 0 {
                                leanh::lean_dec_ref_known(v___x_572_, 1);
                                v___x_573_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_569_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
                                if leanh::lean_obj_tag(v___x_573_) == 0 {
                                    v_a_574_ = leanh::lean_ctor_get(v___x_573_, 0);
                                    leanh::lean_inc(v_a_574_);
                                    leanh::lean_dec_ref_known(v___x_573_, 1);
                                    v_a_551_ = v_a_574_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_575_ = leanh::lean_ctor_get(v___x_573_, 0);
                                    v_isSharedCheck_582_ =
                                        (!leanh::lean_is_exclusive(v___x_573_)) as u8;
                                    if v_isSharedCheck_582_ == 0 {
                                        v___x_577_ = v___x_573_;
                                        v_isShared_578_ = v_isSharedCheck_582_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_575_);
                                        leanh::lean_dec(v___x_573_);
                                        v___x_577_ = leanh::lean_box(0);
                                        v_isShared_578_ = v_isSharedCheck_582_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_mvarId_569_);
                                return v___x_572_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_563_);
                        leanh::lean_dec(v___x_540_);
                        v_a_583_ = leanh::lean_ctor_get(v___x_564_, 0);
                        v_isSharedCheck_590_ = (!leanh::lean_is_exclusive(v___x_564_)) as u8;
                        if v_isSharedCheck_590_ == 0 {
                            v___x_585_ = v___x_564_;
                            v_isShared_586_ = v_isSharedCheck_590_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_583_);
                            leanh::lean_dec(v___x_564_);
                            v___x_585_ = leanh::lean_box(0);
                            v_isShared_586_ = v_isSharedCheck_590_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_540_);
                    leanh::lean_dec(v_a_539_);
                    v_a_591_ = leanh::lean_ctor_get(v___x_562_, 0);
                    v_isSharedCheck_598_ = (!leanh::lean_is_exclusive(v___x_562_)) as u8;
                    if v_isSharedCheck_598_ == 0 {
                        v___x_593_ = v___x_562_;
                        v_isShared_594_ = v_isSharedCheck_598_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_591_);
                        leanh::lean_dec(v___x_562_);
                        v___x_593_ = leanh::lean_box(0);
                        v_isShared_594_ = v_isSharedCheck_598_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_552_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_a_551_, v___y_542_, v___y_545_, v___y_546_, v___y_547_, v___y_548_,
                );
                if leanh::lean_obj_tag(v___x_552_) == 0 {
                    v_isSharedCheck_560_ = (!leanh::lean_is_exclusive(v___x_552_)) as u8;
                    if v_isSharedCheck_560_ == 0 {
                        v_unused_561_ = leanh::lean_ctor_get(v___x_552_, 0);
                        leanh::lean_dec(v_unused_561_);
                        v___x_554_ = v___x_552_;
                        v_isShared_555_ = v_isSharedCheck_560_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_552_);
                        v___x_554_ = leanh::lean_box(0);
                        v_isShared_555_ = v_isSharedCheck_560_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_552_;
                }
            }
            2 => {
                v___x_556_ = leanh::lean_box(0);
                if v_isShared_555_ == 0 {
                    leanh::lean_ctor_set(v___x_554_, 0, v___x_556_);
                    v___x_558_ = v___x_554_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
                    v___x_558_ = v_reuseFailAlloc_559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_558_;
            }
            4 => {
                if v_isShared_578_ == 0 {
                    v___x_580_ = v___x_577_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_581_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
                    v___x_580_ = v_reuseFailAlloc_581_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_580_;
            }
            6 => {
                if v_isShared_586_ == 0 {
                    v___x_588_ = v___x_585_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
                    v___x_588_ = v_reuseFailAlloc_589_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_588_;
            }
            8 => {
                if v_isShared_594_ == 0 {
                    v___x_596_ = v___x_593_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
                    v___x_596_ = v_reuseFailAlloc_597_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjection___lam__0___boxed(
    mut v_a_599_: *mut leanh::LeanObject,
    mut v___x_600_: *mut leanh::LeanObject,
    mut v___y_601_: *mut leanh::LeanObject,
    mut v___y_602_: *mut leanh::LeanObject,
    mut v___y_603_: *mut leanh::LeanObject,
    mut v___y_604_: *mut leanh::LeanObject,
    mut v___y_605_: *mut leanh::LeanObject,
    mut v___y_606_: *mut leanh::LeanObject,
    mut v___y_607_: *mut leanh::LeanObject,
    mut v___y_608_: *mut leanh::LeanObject,
    mut v___y_609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_610_ = l_Lean_Elab_Tactic_evalInjection___lam__0(
        v_a_599_, v___x_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_,
        v___y_606_, v___y_607_, v___y_608_,
    );
    leanh::lean_dec(v___y_608_);
    leanh::lean_dec_ref(v___y_607_);
    leanh::lean_dec(v___y_606_);
    leanh::lean_dec_ref(v___y_605_);
    leanh::lean_dec(v___y_604_);
    leanh::lean_dec_ref(v___y_603_);
    leanh::lean_dec(v___y_602_);
    leanh::lean_dec_ref(v___y_601_);
    return v_res_610_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjection(
    mut v_stx_611_: *mut leanh::LeanObject,
    mut v_a_612_: *mut leanh::LeanObject,
    mut v_a_613_: *mut leanh::LeanObject,
    mut v_a_614_: *mut leanh::LeanObject,
    mut v_a_615_: *mut leanh::LeanObject,
    mut v_a_616_: *mut leanh::LeanObject,
    mut v_a_617_: *mut leanh::LeanObject,
    mut v_a_618_: *mut leanh::LeanObject,
    mut v_a_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_634_: u8 = 0;
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_621_ = leanh::lean_unsigned_to_nat(1);
                v___x_622_ = l_Lean_Syntax_getArg(v_stx_611_, v___x_621_);
                v___x_623_ = leanh::lean_box(0);
                v___x_624_ = l_Lean_Elab_Tactic_elabAsFVar(
                    v___x_622_, v___x_623_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_,
                    v_a_617_, v_a_618_, v_a_619_,
                );
                if leanh::lean_obj_tag(v___x_624_) == 0 {
                    v_a_625_ = leanh::lean_ctor_get(v___x_624_, 0);
                    leanh::lean_inc(v_a_625_);
                    leanh::lean_dec_ref_known(v___x_624_, 1);
                    v___x_626_ = leanh::lean_unsigned_to_nat(2);
                    v___x_627_ = l_Lean_Syntax_getArg(v_stx_611_, v___x_626_);
                    v___x_628_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(v___x_627_);
                    leanh::lean_dec(v___x_627_);
                    v___f_629_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalInjection___lam__0___boxed as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    leanh::lean_closure_set(v___f_629_, 0, v_a_625_);
                    leanh::lean_closure_set(v___f_629_, 1, v___x_628_);
                    v___x_630_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_629_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_,
                        v_a_618_, v_a_619_,
                    );
                    return v___x_630_;
                } else {
                    v_a_631_ = leanh::lean_ctor_get(v___x_624_, 0);
                    v_isSharedCheck_638_ = (!leanh::lean_is_exclusive(v___x_624_)) as u8;
                    if v_isSharedCheck_638_ == 0 {
                        v___x_633_ = v___x_624_;
                        v_isShared_634_ = v_isSharedCheck_638_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_631_);
                        leanh::lean_dec(v___x_624_);
                        v___x_633_ = leanh::lean_box(0);
                        v_isShared_634_ = v_isSharedCheck_638_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_634_ == 0 {
                    v___x_636_ = v___x_633_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_637_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
                    v___x_636_ = v_reuseFailAlloc_637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjection___boxed(
    mut v_stx_639_: *mut leanh::LeanObject,
    mut v_a_640_: *mut leanh::LeanObject,
    mut v_a_641_: *mut leanh::LeanObject,
    mut v_a_642_: *mut leanh::LeanObject,
    mut v_a_643_: *mut leanh::LeanObject,
    mut v_a_644_: *mut leanh::LeanObject,
    mut v_a_645_: *mut leanh::LeanObject,
    mut v_a_646_: *mut leanh::LeanObject,
    mut v_a_647_: *mut leanh::LeanObject,
    mut v_a_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_649_ = l_Lean_Elab_Tactic_evalInjection(
        v_stx_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_,
    );
    leanh::lean_dec(v_a_647_);
    leanh::lean_dec_ref(v_a_646_);
    leanh::lean_dec(v_a_645_);
    leanh::lean_dec_ref(v_a_644_);
    leanh::lean_dec(v_a_643_);
    leanh::lean_dec_ref(v_a_642_);
    leanh::lean_dec(v_a_641_);
    leanh::lean_dec_ref(v_a_640_);
    leanh::lean_dec(v_stx_639_);
    return v_res_649_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1()
-> *mut leanh::LeanObject {
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_667_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3;
    v___x_668_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6;
    v___x_669_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalInjection___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_670_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_666_, v___x_667_, v___x_668_, v___x_669_,
    );
    return v___x_670_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___boxed(
    mut v_a_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_672_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
    return v_res_672_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6;
    v___x_699_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6;
    v___x_700_ = l_Lean_addBuiltinDeclarationRanges(v___x_698_, v___x_699_);
    return v___x_700_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___boxed(
    mut v_a_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_702_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
    return v_res_702_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjections___lam__0(
    mut v_ids_706_: *mut leanh::LeanObject,
    mut v___x_707_: *mut leanh::LeanObject,
    mut v___y_708_: *mut leanh::LeanObject,
    mut v___y_709_: *mut leanh::LeanObject,
    mut v___y_710_: *mut leanh::LeanObject,
    mut v___y_711_: *mut leanh::LeanObject,
    mut v___y_712_: *mut leanh::LeanObject,
    mut v___y_713_: *mut leanh::LeanObject,
    mut v___y_714_: *mut leanh::LeanObject,
    mut v___y_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_727_: u8 = 0;
    let mut v_unused_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remainingNames_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_750_: u8 = 0;
    let mut v_a_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_754_: u8 = 0;
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_758_: u8 = 0;
    let mut v_a_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_762_: u8 = 0;
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_729_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_709_, v___y_712_, v___y_713_, v___y_714_, v___y_715_,
                );
                if leanh::lean_obj_tag(v___x_729_) == 0 {
                    v_a_730_ = leanh::lean_ctor_get(v___x_729_, 0);
                    leanh::lean_inc_n(v_a_730_, 2);
                    leanh::lean_dec_ref_known(v___x_729_, 1);
                    v___x_731_ = leanh::lean_unsigned_to_nat(5);
                    leanh::lean_inc(v_ids_706_);
                    v___x_732_ = l_Lean_Meta_injections(
                        v_a_730_, v_ids_706_, v___x_731_, v___x_707_, v___y_712_, v___y_713_,
                        v___y_714_, v___y_715_,
                    );
                    if leanh::lean_obj_tag(v___x_732_) == 0 {
                        v_a_733_ = leanh::lean_ctor_get(v___x_732_, 0);
                        leanh::lean_inc(v_a_733_);
                        leanh::lean_dec_ref_known(v___x_732_, 1);
                        if leanh::lean_obj_tag(v_a_733_) == 0 {
                            v___x_734_ = l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1;
                            v___x_735_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_734_, v_a_730_, v_ids_706_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
                            if leanh::lean_obj_tag(v___x_735_) == 0 {
                                leanh::lean_dec_ref_known(v___x_735_, 1);
                                v___x_736_ = leanh::lean_box(0);
                                v_a_718_ = v___x_736_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_735_;
                            }
                        } else {
                            leanh::lean_dec(v_ids_706_);
                            v_mvarId_737_ = leanh::lean_ctor_get(v_a_733_, 0);
                            leanh::lean_inc(v_mvarId_737_);
                            v_remainingNames_738_ = leanh::lean_ctor_get(v_a_733_, 1);
                            leanh::lean_inc(v_remainingNames_738_);
                            leanh::lean_dec_ref_known(v_a_733_, 3);
                            v___x_739_ = l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1;
                            v___x_740_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_739_, v_a_730_, v_remainingNames_738_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
                            if leanh::lean_obj_tag(v___x_740_) == 0 {
                                leanh::lean_dec_ref_known(v___x_740_, 1);
                                v___x_741_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_737_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
                                if leanh::lean_obj_tag(v___x_741_) == 0 {
                                    v_a_742_ = leanh::lean_ctor_get(v___x_741_, 0);
                                    leanh::lean_inc(v_a_742_);
                                    leanh::lean_dec_ref_known(v___x_741_, 1);
                                    v_a_718_ = v_a_742_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_743_ = leanh::lean_ctor_get(v___x_741_, 0);
                                    v_isSharedCheck_750_ =
                                        (!leanh::lean_is_exclusive(v___x_741_)) as u8;
                                    if v_isSharedCheck_750_ == 0 {
                                        v___x_745_ = v___x_741_;
                                        v_isShared_746_ = v_isSharedCheck_750_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_743_);
                                        leanh::lean_dec(v___x_741_);
                                        v___x_745_ = leanh::lean_box(0);
                                        v_isShared_746_ = v_isSharedCheck_750_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_mvarId_737_);
                                return v___x_740_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_730_);
                        leanh::lean_dec(v_ids_706_);
                        v_a_751_ = leanh::lean_ctor_get(v___x_732_, 0);
                        v_isSharedCheck_758_ = (!leanh::lean_is_exclusive(v___x_732_)) as u8;
                        if v_isSharedCheck_758_ == 0 {
                            v___x_753_ = v___x_732_;
                            v_isShared_754_ = v_isSharedCheck_758_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_751_);
                            leanh::lean_dec(v___x_732_);
                            v___x_753_ = leanh::lean_box(0);
                            v_isShared_754_ = v_isSharedCheck_758_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_707_);
                    leanh::lean_dec(v_ids_706_);
                    v_a_759_ = leanh::lean_ctor_get(v___x_729_, 0);
                    v_isSharedCheck_766_ = (!leanh::lean_is_exclusive(v___x_729_)) as u8;
                    if v_isSharedCheck_766_ == 0 {
                        v___x_761_ = v___x_729_;
                        v_isShared_762_ = v_isSharedCheck_766_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_759_);
                        leanh::lean_dec(v___x_729_);
                        v___x_761_ = leanh::lean_box(0);
                        v_isShared_762_ = v_isSharedCheck_766_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_719_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_a_718_, v___y_709_, v___y_712_, v___y_713_, v___y_714_, v___y_715_,
                );
                if leanh::lean_obj_tag(v___x_719_) == 0 {
                    v_isSharedCheck_727_ = (!leanh::lean_is_exclusive(v___x_719_)) as u8;
                    if v_isSharedCheck_727_ == 0 {
                        v_unused_728_ = leanh::lean_ctor_get(v___x_719_, 0);
                        leanh::lean_dec(v_unused_728_);
                        v___x_721_ = v___x_719_;
                        v_isShared_722_ = v_isSharedCheck_727_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_719_);
                        v___x_721_ = leanh::lean_box(0);
                        v_isShared_722_ = v_isSharedCheck_727_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_719_;
                }
            }
            2 => {
                v___x_723_ = leanh::lean_box(0);
                if v_isShared_722_ == 0 {
                    leanh::lean_ctor_set(v___x_721_, 0, v___x_723_);
                    v___x_725_ = v___x_721_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_726_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
                    v___x_725_ = v_reuseFailAlloc_726_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_725_;
            }
            4 => {
                if v_isShared_746_ == 0 {
                    v___x_748_ = v___x_745_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
                    v___x_748_ = v_reuseFailAlloc_749_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_748_;
            }
            6 => {
                if v_isShared_754_ == 0 {
                    v___x_756_ = v___x_753_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_757_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
                    v___x_756_ = v_reuseFailAlloc_757_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_756_;
            }
            8 => {
                if v_isShared_762_ == 0 {
                    v___x_764_ = v___x_761_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_765_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
                    v___x_764_ = v_reuseFailAlloc_765_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjections___lam__0___boxed(
    mut v_ids_767_: *mut leanh::LeanObject,
    mut v___x_768_: *mut leanh::LeanObject,
    mut v___y_769_: *mut leanh::LeanObject,
    mut v___y_770_: *mut leanh::LeanObject,
    mut v___y_771_: *mut leanh::LeanObject,
    mut v___y_772_: *mut leanh::LeanObject,
    mut v___y_773_: *mut leanh::LeanObject,
    mut v___y_774_: *mut leanh::LeanObject,
    mut v___y_775_: *mut leanh::LeanObject,
    mut v___y_776_: *mut leanh::LeanObject,
    mut v___y_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Elab_Tactic_evalInjections___lam__0(
        v_ids_767_, v___x_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_,
        v___y_774_, v___y_775_, v___y_776_,
    );
    leanh::lean_dec(v___y_776_);
    leanh::lean_dec_ref(v___y_775_);
    leanh::lean_dec(v___y_774_);
    leanh::lean_dec_ref(v___y_773_);
    leanh::lean_dec(v___y_772_);
    leanh::lean_dec_ref(v___y_771_);
    leanh::lean_dec(v___y_770_);
    leanh::lean_dec_ref(v___y_769_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjections(
    mut v_stx_779_: *mut leanh::LeanObject,
    mut v_a_780_: *mut leanh::LeanObject,
    mut v_a_781_: *mut leanh::LeanObject,
    mut v_a_782_: *mut leanh::LeanObject,
    mut v_a_783_: *mut leanh::LeanObject,
    mut v_a_784_: *mut leanh::LeanObject,
    mut v_a_785_: *mut leanh::LeanObject,
    mut v_a_786_: *mut leanh::LeanObject,
    mut v_a_787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_789_ = leanh::lean_box(1);
    v___x_790_ = leanh::lean_unsigned_to_nat(1);
    v___x_791_ = l_Lean_Syntax_getArg(v_stx_779_, v___x_790_);
    v___x_792_ = l_Lean_Syntax_getArgs(v___x_791_);
    leanh::lean_dec(v___x_791_);
    v___x_793_ = lean_array_to_list(v___x_792_);
    v___x_794_ = leanh::lean_box(0);
    v_ids_795_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(v___x_793_, v___x_794_);
    v___f_796_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalInjections___lam__0___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    leanh::lean_closure_set(v___f_796_, 0, v_ids_795_);
    leanh::lean_closure_set(v___f_796_, 1, v___x_789_);
    v___x_797_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_796_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_,
    );
    return v___x_797_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjections___boxed(
    mut v_stx_798_: *mut leanh::LeanObject,
    mut v_a_799_: *mut leanh::LeanObject,
    mut v_a_800_: *mut leanh::LeanObject,
    mut v_a_801_: *mut leanh::LeanObject,
    mut v_a_802_: *mut leanh::LeanObject,
    mut v_a_803_: *mut leanh::LeanObject,
    mut v_a_804_: *mut leanh::LeanObject,
    mut v_a_805_: *mut leanh::LeanObject,
    mut v_a_806_: *mut leanh::LeanObject,
    mut v_a_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lean_Elab_Tactic_evalInjections(
        v_stx_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_,
    );
    leanh::lean_dec(v_a_806_);
    leanh::lean_dec_ref(v_a_805_);
    leanh::lean_dec(v_a_804_);
    leanh::lean_dec_ref(v_a_803_);
    leanh::lean_dec(v_a_802_);
    leanh::lean_dec_ref(v_a_801_);
    leanh::lean_dec(v_a_800_);
    leanh::lean_dec_ref(v_a_799_);
    leanh::lean_dec(v_stx_798_);
    return v_res_808_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1()
-> *mut leanh::LeanObject {
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_822_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0;
    v___x_823_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2;
    v___x_824_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalInjections___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_825_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_821_, v___x_822_, v___x_823_, v___x_824_,
    );
    return v___x_825_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___boxed(
    mut v_a_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_827_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
    return v_res_827_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2;
    v___x_855_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6;
    v___x_856_ = l_Lean_addBuiltinDeclarationRanges(v___x_854_, v___x_855_);
    return v___x_856_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___boxed(
    mut v_a_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_858_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
    return v_res_858_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Injection(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Injection(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Injection(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Injection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Injection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Injection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Injection(builtin);
}