// Lean compiler output
// Module: Lean.Elab.Tactic.Delta
// Imports: Lean.Meta.Tactic.Delta Lean.Elab.Tactic.Location
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_to_list, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_eqv, lean_name_eq, lean_nat_dec_lt, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_getMainTarget,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    l_Lean_Elab_Tactic_withLocation, runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_FVarId_getDecl___redArg;
use crate::r#gen::Lean::Meta::Tactic::Delta::{
    initialize_Lean_Meta_Tactic_Delta, l_Lean_Meta_deltaExpand,
    runtime_initialize_Lean_Meta_Tactic_Delta,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    l_Lean_MVarId_replaceLocalDeclDefEq, l_Lean_MVarId_replaceTargetDefEq,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_throwTacticEx___redArg;
pub static l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value:
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
    m_data: [100, 101, 108, 116, 97, 0],
};
static mut l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        2820377975091604199 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        100, 105, 100, 32, 110, 111, 116, 32, 100, 101, 108, 116, 97, 32, 114, 101, 100, 117, 99,
        101, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 97, 116, 32, 0],
};
static mut l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__0_value) as *mut leanh::LeanObject,11520586616343720014 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 68, 101, 108, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__4_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__5_value) as *mut leanh::LeanObject,17307684298627856868 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [34, 100, 101, 108, 116, 97, 32, 34, 32, 105, 100, 101, 110, 116, 43, 32, 40, 108, 111, 99, 97, 116, 105, 111, 110, 41, 63, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 35 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 65 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__0_value) as *mut leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__1_value) as *mut leanh::LeanObject,((( 65 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__3_value) as *mut leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__4_value) as *mut leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(
    mut v_a_451_: *mut leanh::LeanObject,
    mut v_as_452_: *mut leanh::LeanObject,
    mut v_i_453_: usize,
    mut v_stop_454_: usize,
) -> u8 {
    let mut v___x_455_: u8 = 0;
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: u8 = 0;
    let mut v___x_458_: usize = 0;
    let mut v___x_459_: usize = 0;
    let mut v___x_461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_455_ = lean_usize_dec_eq(v_i_453_, v_stop_454_);
                if v___x_455_ == 0 {
                    v___x_456_ = lean_array_uget_borrowed(v_as_452_, v_i_453_);
                    v___x_457_ = lean_name_eq(v_a_451_, v___x_456_);
                    if v___x_457_ == 0 {
                        v___x_458_ = 1usize;
                        v___x_459_ = lean_usize_add(v_i_453_, v___x_458_);
                        v_i_453_ = v___x_459_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_457_;
                    }
                } else {
                    v___x_461_ = 0;
                    return v___x_461_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0___boxed(
    mut v_a_462_: *mut leanh::LeanObject,
    mut v_as_463_: *mut leanh::LeanObject,
    mut v_i_464_: *mut leanh::LeanObject,
    mut v_stop_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_466_: usize = 0;
    let mut v_stop_boxed_467_: usize = 0;
    let mut v_res_468_: u8 = 0;
    let mut v_r_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_466_ = leanh::lean_unbox_usize(v_i_464_);
    leanh::lean_dec(v_i_464_);
    v_stop_boxed_467_ = leanh::lean_unbox_usize(v_stop_465_);
    leanh::lean_dec(v_stop_465_);
    v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(v_a_462_, v_as_463_, v_i_boxed_466_, v_stop_boxed_467_);
    leanh::lean_dec_ref(v_as_463_);
    leanh::lean_dec(v_a_462_);
    v_r_469_ = leanh::lean_box((v_res_468_) as usize);
    return v_r_469_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(
    mut v_as_470_: *mut leanh::LeanObject,
    mut v_a_471_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: u8 = 0;
    v___x_472_ = leanh::lean_unsigned_to_nat(0);
    v___x_473_ = lean_array_get_size(v_as_470_);
    v___x_474_ = lean_nat_dec_lt(v___x_472_, v___x_473_);
    if v___x_474_ == 0 {
        return v___x_474_;
    } else {
        if v___x_474_ == 0 {
            return v___x_474_;
        } else {
            let mut v___x_475_: usize = 0;
            let mut v___x_476_: usize = 0;
            let mut v___x_477_: u8 = 0;
            v___x_475_ = 0usize;
            v___x_476_ = lean_usize_of_nat(v___x_473_);
            v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0_spec__0(v_a_471_, v_as_470_, v___x_475_, v___x_476_);
            return v___x_477_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0___boxed(
    mut v_as_478_: *mut leanh::LeanObject,
    mut v_a_479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_480_: u8 = 0;
    let mut v_r_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_480_ =
        l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(v_as_478_, v_a_479_);
    leanh::lean_dec(v_a_479_);
    leanh::lean_dec_ref(v_as_478_);
    v_r_481_ = leanh::lean_box((v_res_480_) as usize);
    return v_r_481_;
}
pub unsafe fn l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0(
    mut v_declNames_482_: *mut leanh::LeanObject,
    mut v___y_483_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_484_: u8 = 0;
    v___x_484_ = l_Array_contains___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__0(
        v_declNames_482_,
        v___y_483_,
    );
    return v___x_484_;
}
pub unsafe fn l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed(
    mut v_declNames_485_: *mut leanh::LeanObject,
    mut v___y_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_487_: u8 = 0;
    let mut v_r_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0(v_declNames_485_, v___y_486_);
    leanh::lean_dec(v___y_486_);
    leanh::lean_dec_ref(v_declNames_485_);
    v_r_488_ = leanh::lean_box((v_res_487_) as usize);
    return v_r_488_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(
    mut v_a_489_: *mut leanh::LeanObject,
    mut v_a_490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_496_: u8 = 0;
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_489_) == 0 {
                    v___x_491_ = l_List_reverse___redArg(v_a_490_);
                    return v___x_491_;
                } else {
                    v_head_492_ = leanh::lean_ctor_get(v_a_489_, 0);
                    v_tail_493_ = leanh::lean_ctor_get(v_a_489_, 1);
                    v_isSharedCheck_502_ = (!leanh::lean_is_exclusive(v_a_489_)) as u8;
                    if v_isSharedCheck_502_ == 0 {
                        v___x_495_ = v_a_489_;
                        v_isShared_496_ = v_isSharedCheck_502_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_493_);
                        leanh::lean_inc(v_head_492_);
                        leanh::lean_dec(v_a_489_);
                        v___x_495_ = leanh::lean_box(0);
                        v_isShared_496_ = v_isSharedCheck_502_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_497_ = l_Lean_MessageData_ofName(v_head_492_);
                if v_isShared_496_ == 0 {
                    leanh::lean_ctor_set(v___x_495_, 1, v_a_490_);
                    leanh::lean_ctor_set(v___x_495_, 0, v___x_497_);
                    v___x_499_ = v___x_495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_501_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_501_, 1, v_a_490_);
                    v___x_499_ = v_reuseFailAlloc_501_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_489_ = v_tail_493_;
                v_a_490_ = v___x_499_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_507_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__2;
    v___x_508_ = l_Lean_stringToMessageData(v___x_507_);
    return v___x_508_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_510_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__4;
    v___x_511_ = l_Lean_stringToMessageData(v___x_510_);
    return v___x_511_;
}
pub unsafe fn l_Lean_Elab_Tactic_deltaLocalDecl___redArg(
    mut v_declNames_512_: *mut leanh::LeanObject,
    mut v_fvarId_513_: *mut leanh::LeanObject,
    mut v_a_514_: *mut leanh::LeanObject,
    mut v_a_515_: *mut leanh::LeanObject,
    mut v_a_516_: *mut leanh::LeanObject,
    mut v_a_517_: *mut leanh::LeanObject,
    mut v_a_518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: u8 = 0;
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_543_: u8 = 0;
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_547_: u8 = 0;
    let mut v___x_548_: u8 = 0;
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_a_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_578_: u8 = 0;
    let mut v_a_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_582_: u8 = 0;
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_520_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_,
                );
                if leanh::lean_obj_tag(v___x_520_) == 0 {
                    v_a_521_ = leanh::lean_ctor_get(v___x_520_, 0);
                    leanh::lean_inc(v_a_521_);
                    leanh::lean_dec_ref_known(v___x_520_, 1);
                    leanh::lean_inc(v_fvarId_513_);
                    v___x_522_ =
                        l_Lean_FVarId_getDecl___redArg(v_fvarId_513_, v_a_515_, v_a_517_, v_a_518_);
                    if leanh::lean_obj_tag(v___x_522_) == 0 {
                        v_a_523_ = leanh::lean_ctor_get(v___x_522_, 0);
                        leanh::lean_inc(v_a_523_);
                        leanh::lean_dec_ref_known(v___x_522_, 1);
                        leanh::lean_inc_ref(v_declNames_512_);
                        v___f_524_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_524_, 0, v_declNames_512_);
                        v___x_525_ = l_Lean_LocalDecl_type(v_a_523_);
                        v___x_526_ = 0;
                        leanh::lean_inc_ref(v___x_525_);
                        v___x_527_ = l_Lean_Meta_deltaExpand(
                            v___x_525_, v___f_524_, v___x_526_, v_a_517_, v_a_518_,
                        );
                        if leanh::lean_obj_tag(v___x_527_) == 0 {
                            v_a_528_ = leanh::lean_ctor_get(v___x_527_, 0);
                            leanh::lean_inc(v_a_528_);
                            leanh::lean_dec_ref_known(v___x_527_, 1);
                            v___x_548_ = lean_expr_eqv(v_a_528_, v___x_525_);
                            leanh::lean_dec_ref(v___x_525_);
                            if v___x_548_ == 0 {
                                leanh::lean_dec(v_a_523_);
                                leanh::lean_dec_ref(v_declNames_512_);
                                v___y_530_ = v_a_514_;
                                v___y_531_ = v_a_515_;
                                v___y_532_ = v_a_516_;
                                v___y_533_ = v_a_517_;
                                v___y_534_ = v_a_518_;
                                state = 1;
                                continue;
                            } else {
                                v___x_549_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1;
                                v___x_550_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once
                                    ),
                                    _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3,
                                );
                                v___x_551_ = lean_array_to_list(v_declNames_512_);
                                v___x_552_ = leanh::lean_box(0);
                                v___x_553_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_551_, v___x_552_);
                                v___x_554_ = l_Lean_MessageData_ofList(v___x_553_);
                                v___x_555_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_555_, 0, v___x_550_);
                                leanh::lean_ctor_set(v___x_555_, 1, v___x_554_);
                                v___x_556_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5_once
                                    ),
                                    _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__5,
                                );
                                v___x_557_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_557_, 0, v___x_555_);
                                leanh::lean_ctor_set(v___x_557_, 1, v___x_556_);
                                v___x_558_ = l_Lean_LocalDecl_userName(v_a_523_);
                                leanh::lean_dec(v_a_523_);
                                v___x_559_ = l_Lean_MessageData_ofName(v___x_558_);
                                v___x_560_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_560_, 0, v___x_557_);
                                leanh::lean_ctor_set(v___x_560_, 1, v___x_559_);
                                v___x_561_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_561_, 0, v___x_560_);
                                leanh::lean_inc(v_a_521_);
                                v___x_562_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_549_, v_a_521_, v___x_561_, v_a_515_, v_a_516_, v_a_517_,
                                    v_a_518_,
                                );
                                if leanh::lean_obj_tag(v___x_562_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_562_, 1);
                                    v___y_530_ = v_a_514_;
                                    v___y_531_ = v_a_515_;
                                    v___y_532_ = v_a_516_;
                                    v___y_533_ = v_a_517_;
                                    v___y_534_ = v_a_518_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_528_);
                                    leanh::lean_dec(v_a_521_);
                                    leanh::lean_dec(v_fvarId_513_);
                                    return v___x_562_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_525_);
                            leanh::lean_dec(v_a_523_);
                            leanh::lean_dec(v_a_521_);
                            leanh::lean_dec(v_fvarId_513_);
                            leanh::lean_dec_ref(v_declNames_512_);
                            v_a_563_ = leanh::lean_ctor_get(v___x_527_, 0);
                            v_isSharedCheck_570_ =
                                (!leanh::lean_is_exclusive(v___x_527_)) as u8;
                            if v_isSharedCheck_570_ == 0 {
                                v___x_565_ = v___x_527_;
                                v_isShared_566_ = v_isSharedCheck_570_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_563_);
                                leanh::lean_dec(v___x_527_);
                                v___x_565_ = leanh::lean_box(0);
                                v_isShared_566_ = v_isSharedCheck_570_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_521_);
                        leanh::lean_dec(v_fvarId_513_);
                        leanh::lean_dec_ref(v_declNames_512_);
                        v_a_571_ = leanh::lean_ctor_get(v___x_522_, 0);
                        v_isSharedCheck_578_ = (!leanh::lean_is_exclusive(v___x_522_)) as u8;
                        if v_isSharedCheck_578_ == 0 {
                            v___x_573_ = v___x_522_;
                            v_isShared_574_ = v_isSharedCheck_578_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_571_);
                            leanh::lean_dec(v___x_522_);
                            v___x_573_ = leanh::lean_box(0);
                            v_isShared_574_ = v_isSharedCheck_578_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fvarId_513_);
                    leanh::lean_dec_ref(v_declNames_512_);
                    v_a_579_ = leanh::lean_ctor_get(v___x_520_, 0);
                    v_isSharedCheck_586_ = (!leanh::lean_is_exclusive(v___x_520_)) as u8;
                    if v_isSharedCheck_586_ == 0 {
                        v___x_581_ = v___x_520_;
                        v_isShared_582_ = v_isSharedCheck_586_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_579_);
                        leanh::lean_dec(v___x_520_);
                        v___x_581_ = leanh::lean_box(0);
                        v_isShared_582_ = v_isSharedCheck_586_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_535_ = l_Lean_MVarId_replaceLocalDeclDefEq(
                    v_a_521_,
                    v_fvarId_513_,
                    v_a_528_,
                    v___y_531_,
                    v___y_532_,
                    v___y_533_,
                    v___y_534_,
                );
                if leanh::lean_obj_tag(v___x_535_) == 0 {
                    v_a_536_ = leanh::lean_ctor_get(v___x_535_, 0);
                    leanh::lean_inc(v_a_536_);
                    leanh::lean_dec_ref_known(v___x_535_, 1);
                    v___x_537_ = leanh::lean_box(0);
                    v___x_538_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_538_, 0, v_a_536_);
                    leanh::lean_ctor_set(v___x_538_, 1, v___x_537_);
                    v___x_539_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_538_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_,
                    );
                    return v___x_539_;
                } else {
                    v_a_540_ = leanh::lean_ctor_get(v___x_535_, 0);
                    v_isSharedCheck_547_ = (!leanh::lean_is_exclusive(v___x_535_)) as u8;
                    if v_isSharedCheck_547_ == 0 {
                        v___x_542_ = v___x_535_;
                        v_isShared_543_ = v_isSharedCheck_547_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_540_);
                        leanh::lean_dec(v___x_535_);
                        v___x_542_ = leanh::lean_box(0);
                        v_isShared_543_ = v_isSharedCheck_547_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_543_ == 0 {
                    v___x_545_ = v___x_542_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_546_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
                    v___x_545_ = v_reuseFailAlloc_546_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_545_;
            }
            4 => {
                if v_isShared_566_ == 0 {
                    v___x_568_ = v___x_565_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_569_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
                    v___x_568_ = v_reuseFailAlloc_569_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_568_;
            }
            6 => {
                if v_isShared_574_ == 0 {
                    v___x_576_ = v___x_573_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_576_;
            }
            8 => {
                if v_isShared_582_ == 0 {
                    v___x_584_ = v___x_581_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
                    v___x_584_ = v_reuseFailAlloc_585_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_deltaLocalDecl___redArg___boxed(
    mut v_declNames_587_: *mut leanh::LeanObject,
    mut v_fvarId_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
    mut v_a_590_: *mut leanh::LeanObject,
    mut v_a_591_: *mut leanh::LeanObject,
    mut v_a_592_: *mut leanh::LeanObject,
    mut v_a_593_: *mut leanh::LeanObject,
    mut v_a_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_595_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(
        v_declNames_587_,
        v_fvarId_588_,
        v_a_589_,
        v_a_590_,
        v_a_591_,
        v_a_592_,
        v_a_593_,
    );
    leanh::lean_dec(v_a_593_);
    leanh::lean_dec_ref(v_a_592_);
    leanh::lean_dec(v_a_591_);
    leanh::lean_dec_ref(v_a_590_);
    leanh::lean_dec(v_a_589_);
    return v_res_595_;
}
pub unsafe fn l_Lean_Elab_Tactic_deltaLocalDecl(
    mut v_declNames_596_: *mut leanh::LeanObject,
    mut v_fvarId_597_: *mut leanh::LeanObject,
    mut v_a_598_: *mut leanh::LeanObject,
    mut v_a_599_: *mut leanh::LeanObject,
    mut v_a_600_: *mut leanh::LeanObject,
    mut v_a_601_: *mut leanh::LeanObject,
    mut v_a_602_: *mut leanh::LeanObject,
    mut v_a_603_: *mut leanh::LeanObject,
    mut v_a_604_: *mut leanh::LeanObject,
    mut v_a_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_607_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg(
        v_declNames_596_,
        v_fvarId_597_,
        v_a_599_,
        v_a_602_,
        v_a_603_,
        v_a_604_,
        v_a_605_,
    );
    return v___x_607_;
}
pub unsafe fn l_Lean_Elab_Tactic_deltaLocalDecl___boxed(
    mut v_declNames_608_: *mut leanh::LeanObject,
    mut v_fvarId_609_: *mut leanh::LeanObject,
    mut v_a_610_: *mut leanh::LeanObject,
    mut v_a_611_: *mut leanh::LeanObject,
    mut v_a_612_: *mut leanh::LeanObject,
    mut v_a_613_: *mut leanh::LeanObject,
    mut v_a_614_: *mut leanh::LeanObject,
    mut v_a_615_: *mut leanh::LeanObject,
    mut v_a_616_: *mut leanh::LeanObject,
    mut v_a_617_: *mut leanh::LeanObject,
    mut v_a_618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_619_ = l_Lean_Elab_Tactic_deltaLocalDecl(
        v_declNames_608_,
        v_fvarId_609_,
        v_a_610_,
        v_a_611_,
        v_a_612_,
        v_a_613_,
        v_a_614_,
        v_a_615_,
        v_a_616_,
        v_a_617_,
    );
    leanh::lean_dec(v_a_617_);
    leanh::lean_dec_ref(v_a_616_);
    leanh::lean_dec(v_a_615_);
    leanh::lean_dec_ref(v_a_614_);
    leanh::lean_dec(v_a_613_);
    leanh::lean_dec_ref(v_a_612_);
    leanh::lean_dec(v_a_611_);
    leanh::lean_dec_ref(v_a_610_);
    return v_res_619_;
}
pub unsafe fn l_Lean_Elab_Tactic_deltaTarget(
    mut v_declNames_620_: *mut leanh::LeanObject,
    mut v_a_621_: *mut leanh::LeanObject,
    mut v_a_622_: *mut leanh::LeanObject,
    mut v_a_623_: *mut leanh::LeanObject,
    mut v_a_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
    mut v_a_626_: *mut leanh::LeanObject,
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_652_: u8 = 0;
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v___x_657_: u8 = 0;
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut v_a_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut v_a_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_686_: u8 = 0;
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_690_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_630_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_622_, v_a_625_, v_a_626_, v_a_627_, v_a_628_,
                );
                if leanh::lean_obj_tag(v___x_630_) == 0 {
                    v_a_631_ = leanh::lean_ctor_get(v___x_630_, 0);
                    leanh::lean_inc(v_a_631_);
                    leanh::lean_dec_ref_known(v___x_630_, 1);
                    v___x_632_ = l_Lean_Elab_Tactic_getMainTarget(
                        v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_,
                        v_a_628_,
                    );
                    if leanh::lean_obj_tag(v___x_632_) == 0 {
                        v_a_633_ = leanh::lean_ctor_get(v___x_632_, 0);
                        leanh::lean_inc_n(v_a_633_, 2);
                        leanh::lean_dec_ref_known(v___x_632_, 1);
                        leanh::lean_inc_ref(v_declNames_620_);
                        v___f_634_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_deltaLocalDecl___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_634_, 0, v_declNames_620_);
                        v___x_635_ = 0;
                        v___x_636_ = l_Lean_Meta_deltaExpand(
                            v_a_633_, v___f_634_, v___x_635_, v_a_627_, v_a_628_,
                        );
                        if leanh::lean_obj_tag(v___x_636_) == 0 {
                            v_a_637_ = leanh::lean_ctor_get(v___x_636_, 0);
                            leanh::lean_inc(v_a_637_);
                            leanh::lean_dec_ref_known(v___x_636_, 1);
                            v___x_657_ = lean_expr_eqv(v_a_637_, v_a_633_);
                            leanh::lean_dec(v_a_633_);
                            if v___x_657_ == 0 {
                                leanh::lean_dec_ref(v_declNames_620_);
                                v___y_639_ = v_a_622_;
                                v___y_640_ = v_a_625_;
                                v___y_641_ = v_a_626_;
                                v___y_642_ = v_a_627_;
                                v___y_643_ = v_a_628_;
                                state = 1;
                                continue;
                            } else {
                                v___x_658_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1;
                                v___x_659_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once
                                    ),
                                    _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3,
                                );
                                v___x_660_ = lean_array_to_list(v_declNames_620_);
                                v___x_661_ = leanh::lean_box(0);
                                v___x_662_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_660_, v___x_661_);
                                v___x_663_ = l_Lean_MessageData_ofList(v___x_662_);
                                v___x_664_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_664_, 0, v___x_659_);
                                leanh::lean_ctor_set(v___x_664_, 1, v___x_663_);
                                v___x_665_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_665_, 0, v___x_664_);
                                leanh::lean_inc(v_a_631_);
                                v___x_666_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_658_, v_a_631_, v___x_665_, v_a_625_, v_a_626_, v_a_627_,
                                    v_a_628_,
                                );
                                if leanh::lean_obj_tag(v___x_666_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_666_, 1);
                                    v___y_639_ = v_a_622_;
                                    v___y_640_ = v_a_625_;
                                    v___y_641_ = v_a_626_;
                                    v___y_642_ = v_a_627_;
                                    v___y_643_ = v_a_628_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_637_);
                                    leanh::lean_dec(v_a_631_);
                                    return v___x_666_;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_633_);
                            leanh::lean_dec(v_a_631_);
                            leanh::lean_dec_ref(v_declNames_620_);
                            v_a_667_ = leanh::lean_ctor_get(v___x_636_, 0);
                            v_isSharedCheck_674_ =
                                (!leanh::lean_is_exclusive(v___x_636_)) as u8;
                            if v_isSharedCheck_674_ == 0 {
                                v___x_669_ = v___x_636_;
                                v_isShared_670_ = v_isSharedCheck_674_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_667_);
                                leanh::lean_dec(v___x_636_);
                                v___x_669_ = leanh::lean_box(0);
                                v_isShared_670_ = v_isSharedCheck_674_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_631_);
                        leanh::lean_dec_ref(v_declNames_620_);
                        v_a_675_ = leanh::lean_ctor_get(v___x_632_, 0);
                        v_isSharedCheck_682_ = (!leanh::lean_is_exclusive(v___x_632_)) as u8;
                        if v_isSharedCheck_682_ == 0 {
                            v___x_677_ = v___x_632_;
                            v_isShared_678_ = v_isSharedCheck_682_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_675_);
                            leanh::lean_dec(v___x_632_);
                            v___x_677_ = leanh::lean_box(0);
                            v_isShared_678_ = v_isSharedCheck_682_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_declNames_620_);
                    v_a_683_ = leanh::lean_ctor_get(v___x_630_, 0);
                    v_isSharedCheck_690_ = (!leanh::lean_is_exclusive(v___x_630_)) as u8;
                    if v_isSharedCheck_690_ == 0 {
                        v___x_685_ = v___x_630_;
                        v_isShared_686_ = v_isSharedCheck_690_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_683_);
                        leanh::lean_dec(v___x_630_);
                        v___x_685_ = leanh::lean_box(0);
                        v_isShared_686_ = v_isSharedCheck_690_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_644_ = l_Lean_MVarId_replaceTargetDefEq(
                    v_a_631_, v_a_637_, v___y_640_, v___y_641_, v___y_642_, v___y_643_,
                );
                if leanh::lean_obj_tag(v___x_644_) == 0 {
                    v_a_645_ = leanh::lean_ctor_get(v___x_644_, 0);
                    leanh::lean_inc(v_a_645_);
                    leanh::lean_dec_ref_known(v___x_644_, 1);
                    v___x_646_ = leanh::lean_box(0);
                    v___x_647_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_647_, 0, v_a_645_);
                    leanh::lean_ctor_set(v___x_647_, 1, v___x_646_);
                    v___x_648_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_647_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_,
                    );
                    return v___x_648_;
                } else {
                    v_a_649_ = leanh::lean_ctor_get(v___x_644_, 0);
                    v_isSharedCheck_656_ = (!leanh::lean_is_exclusive(v___x_644_)) as u8;
                    if v_isSharedCheck_656_ == 0 {
                        v___x_651_ = v___x_644_;
                        v_isShared_652_ = v_isSharedCheck_656_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_649_);
                        leanh::lean_dec(v___x_644_);
                        v___x_651_ = leanh::lean_box(0);
                        v_isShared_652_ = v_isSharedCheck_656_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_652_ == 0 {
                    v___x_654_ = v___x_651_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
                    v___x_654_ = v_reuseFailAlloc_655_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_654_;
            }
            4 => {
                if v_isShared_670_ == 0 {
                    v___x_672_ = v___x_669_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
                    v___x_672_ = v_reuseFailAlloc_673_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_672_;
            }
            6 => {
                if v_isShared_678_ == 0 {
                    v___x_680_ = v___x_677_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_681_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
                    v___x_680_ = v_reuseFailAlloc_681_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_680_;
            }
            8 => {
                if v_isShared_686_ == 0 {
                    v___x_688_ = v___x_685_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_689_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
                    v___x_688_ = v_reuseFailAlloc_689_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_deltaTarget___boxed(
    mut v_declNames_691_: *mut leanh::LeanObject,
    mut v_a_692_: *mut leanh::LeanObject,
    mut v_a_693_: *mut leanh::LeanObject,
    mut v_a_694_: *mut leanh::LeanObject,
    mut v_a_695_: *mut leanh::LeanObject,
    mut v_a_696_: *mut leanh::LeanObject,
    mut v_a_697_: *mut leanh::LeanObject,
    mut v_a_698_: *mut leanh::LeanObject,
    mut v_a_699_: *mut leanh::LeanObject,
    mut v_a_700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Lean_Elab_Tactic_deltaTarget(
        v_declNames_691_,
        v_a_692_,
        v_a_693_,
        v_a_694_,
        v_a_695_,
        v_a_696_,
        v_a_697_,
        v_a_698_,
        v_a_699_,
    );
    leanh::lean_dec(v_a_699_);
    leanh::lean_dec_ref(v_a_698_);
    leanh::lean_dec(v_a_697_);
    leanh::lean_dec_ref(v_a_696_);
    leanh::lean_dec(v_a_695_);
    leanh::lean_dec_ref(v_a_694_);
    leanh::lean_dec(v_a_693_);
    leanh::lean_dec_ref(v_a_692_);
    return v_res_701_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDelta___lam__0(
    mut v_a_702_: *mut leanh::LeanObject,
    mut v_x_703_: *mut leanh::LeanObject,
    mut v___y_704_: *mut leanh::LeanObject,
    mut v___y_705_: *mut leanh::LeanObject,
    mut v___y_706_: *mut leanh::LeanObject,
    mut v___y_707_: *mut leanh::LeanObject,
    mut v___y_708_: *mut leanh::LeanObject,
    mut v___y_709_: *mut leanh::LeanObject,
    mut v___y_710_: *mut leanh::LeanObject,
    mut v___y_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__1;
    v___x_714_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3_once),
        _init_l_Lean_Elab_Tactic_deltaLocalDecl___redArg___closed__3,
    );
    v___x_715_ = lean_array_to_list(v_a_702_);
    v___x_716_ = leanh::lean_box(0);
    v___x_717_ =
        l_List_mapTR_loop___at___00Lean_Elab_Tactic_deltaLocalDecl_spec__1(v___x_715_, v___x_716_);
    v___x_718_ = l_Lean_MessageData_ofList(v___x_717_);
    v___x_719_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_719_, 0, v___x_714_);
    leanh::lean_ctor_set(v___x_719_, 1, v___x_718_);
    v___x_720_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_720_, 0, v___x_719_);
    v___x_721_ = l_Lean_Meta_throwTacticEx___redArg(
        v___x_713_, v_x_703_, v___x_720_, v___y_708_, v___y_709_, v___y_710_, v___y_711_,
    );
    return v___x_721_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDelta___lam__0___boxed(
    mut v_a_722_: *mut leanh::LeanObject,
    mut v_x_723_: *mut leanh::LeanObject,
    mut v___y_724_: *mut leanh::LeanObject,
    mut v___y_725_: *mut leanh::LeanObject,
    mut v___y_726_: *mut leanh::LeanObject,
    mut v___y_727_: *mut leanh::LeanObject,
    mut v___y_728_: *mut leanh::LeanObject,
    mut v___y_729_: *mut leanh::LeanObject,
    mut v___y_730_: *mut leanh::LeanObject,
    mut v___y_731_: *mut leanh::LeanObject,
    mut v___y_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Lean_Elab_Tactic_evalDelta___lam__0(
        v_a_722_, v_x_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_,
        v___y_730_, v___y_731_,
    );
    leanh::lean_dec(v___y_731_);
    leanh::lean_dec_ref(v___y_730_);
    leanh::lean_dec(v___y_729_);
    leanh::lean_dec_ref(v___y_728_);
    leanh::lean_dec(v___y_727_);
    leanh::lean_dec_ref(v___y_726_);
    leanh::lean_dec(v___y_725_);
    leanh::lean_dec_ref(v___y_724_);
    return v_res_733_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(
    mut v_sz_734_: usize,
    mut v_i_735_: usize,
    mut v_bs_736_: *mut leanh::LeanObject,
    mut v___y_737_: *mut leanh::LeanObject,
    mut v___y_738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_740_: u8 = 0;
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: usize = 0;
    let mut v___x_749_: usize = 0;
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_755_: u8 = 0;
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_740_ = lean_usize_dec_lt(v_i_735_, v_sz_734_);
                if v___x_740_ == 0 {
                    v___x_741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_741_, 0, v_bs_736_);
                    return v___x_741_;
                } else {
                    v_v_742_ = lean_array_uget_borrowed(v_bs_736_, v_i_735_);
                    v___x_743_ = leanh::lean_box(0);
                    leanh::lean_inc(v_v_742_);
                    v___x_744_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_v_742_, v___x_743_, v___y_737_, v___y_738_,
                    );
                    if leanh::lean_obj_tag(v___x_744_) == 0 {
                        v_a_745_ = leanh::lean_ctor_get(v___x_744_, 0);
                        leanh::lean_inc(v_a_745_);
                        leanh::lean_dec_ref_known(v___x_744_, 1);
                        v___x_746_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_747_ = lean_array_uset(v_bs_736_, v_i_735_, v___x_746_);
                        v___x_748_ = 1usize;
                        v___x_749_ = lean_usize_add(v_i_735_, v___x_748_);
                        v___x_750_ = lean_array_uset(v_bs_x27_747_, v_i_735_, v_a_745_);
                        v_i_735_ = v___x_749_;
                        v_bs_736_ = v___x_750_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_736_);
                        v_a_752_ = leanh::lean_ctor_get(v___x_744_, 0);
                        v_isSharedCheck_759_ = (!leanh::lean_is_exclusive(v___x_744_)) as u8;
                        if v_isSharedCheck_759_ == 0 {
                            v___x_754_ = v___x_744_;
                            v_isShared_755_ = v_isSharedCheck_759_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_752_);
                            leanh::lean_dec(v___x_744_);
                            v___x_754_ = leanh::lean_box(0);
                            v_isShared_755_ = v_isSharedCheck_759_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_755_ == 0 {
                    v___x_757_ = v___x_754_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
                    v___x_757_ = v_reuseFailAlloc_758_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg___boxed(
    mut v_sz_760_: *mut leanh::LeanObject,
    mut v_i_761_: *mut leanh::LeanObject,
    mut v_bs_762_: *mut leanh::LeanObject,
    mut v___y_763_: *mut leanh::LeanObject,
    mut v___y_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_766_: usize = 0;
    let mut v_i_boxed_767_: usize = 0;
    let mut v_res_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_766_ = leanh::lean_unbox_usize(v_sz_760_);
    leanh::lean_dec(v_sz_760_);
    v_i_boxed_767_ = leanh::lean_unbox_usize(v_i_761_);
    leanh::lean_dec(v_i_761_);
    v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_boxed_766_, v_i_boxed_767_, v_bs_762_, v___y_763_, v___y_764_);
    leanh::lean_dec(v___y_764_);
    leanh::lean_dec_ref(v___y_763_);
    return v_res_768_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDelta(
    mut v_stx_769_: *mut leanh::LeanObject,
    mut v_a_770_: *mut leanh::LeanObject,
    mut v_a_771_: *mut leanh::LeanObject,
    mut v_a_772_: *mut leanh::LeanObject,
    mut v_a_773_: *mut leanh::LeanObject,
    mut v_a_774_: *mut leanh::LeanObject,
    mut v_a_775_: *mut leanh::LeanObject,
    mut v_a_776_: *mut leanh::LeanObject,
    mut v_a_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_782_: usize = 0;
    let mut v___x_783_: usize = 0;
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_796_: u8 = 0;
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_779_ = leanh::lean_unsigned_to_nat(1);
                v___x_780_ = l_Lean_Syntax_getArg(v_stx_769_, v___x_779_);
                v___x_781_ = l_Lean_Syntax_getArgs(v___x_780_);
                leanh::lean_dec(v___x_780_);
                v_sz_782_ = lean_array_size(v___x_781_);
                v___x_783_ = 0usize;
                v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_782_, v___x_783_, v___x_781_, v_a_776_, v_a_777_);
                if leanh::lean_obj_tag(v___x_784_) == 0 {
                    v_a_785_ = leanh::lean_ctor_get(v___x_784_, 0);
                    leanh::lean_inc_n(v_a_785_, 3);
                    leanh::lean_dec_ref_known(v___x_784_, 1);
                    v___f_786_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalDelta___lam__0___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    leanh::lean_closure_set(v___f_786_, 0, v_a_785_);
                    v___x_787_ = leanh::lean_unsigned_to_nat(2);
                    v___x_788_ = l_Lean_Syntax_getArg(v_stx_769_, v___x_787_);
                    v___x_789_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_788_);
                    leanh::lean_dec(v___x_788_);
                    v___x_790_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_deltaLocalDecl___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    leanh::lean_closure_set(v___x_790_, 0, v_a_785_);
                    v___x_791_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_deltaTarget___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    leanh::lean_closure_set(v___x_791_, 0, v_a_785_);
                    v___x_792_ = l_Lean_Elab_Tactic_withLocation(
                        v___x_789_, v___x_790_, v___x_791_, v___f_786_, v_a_770_, v_a_771_,
                        v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_,
                    );
                    leanh::lean_dec(v___x_789_);
                    return v___x_792_;
                } else {
                    v_a_793_ = leanh::lean_ctor_get(v___x_784_, 0);
                    v_isSharedCheck_800_ = (!leanh::lean_is_exclusive(v___x_784_)) as u8;
                    if v_isSharedCheck_800_ == 0 {
                        v___x_795_ = v___x_784_;
                        v_isShared_796_ = v_isSharedCheck_800_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_793_);
                        leanh::lean_dec(v___x_784_);
                        v___x_795_ = leanh::lean_box(0);
                        v_isShared_796_ = v_isSharedCheck_800_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_796_ == 0 {
                    v___x_798_ = v___x_795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_799_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
                    v___x_798_ = v_reuseFailAlloc_799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalDelta___boxed(
    mut v_stx_801_: *mut leanh::LeanObject,
    mut v_a_802_: *mut leanh::LeanObject,
    mut v_a_803_: *mut leanh::LeanObject,
    mut v_a_804_: *mut leanh::LeanObject,
    mut v_a_805_: *mut leanh::LeanObject,
    mut v_a_806_: *mut leanh::LeanObject,
    mut v_a_807_: *mut leanh::LeanObject,
    mut v_a_808_: *mut leanh::LeanObject,
    mut v_a_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l_Lean_Elab_Tactic_evalDelta(
        v_stx_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_,
    );
    leanh::lean_dec(v_a_809_);
    leanh::lean_dec_ref(v_a_808_);
    leanh::lean_dec(v_a_807_);
    leanh::lean_dec_ref(v_a_806_);
    leanh::lean_dec(v_a_805_);
    leanh::lean_dec_ref(v_a_804_);
    leanh::lean_dec(v_a_803_);
    leanh::lean_dec_ref(v_a_802_);
    leanh::lean_dec(v_stx_801_);
    return v_res_811_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(
    mut v_sz_812_: usize,
    mut v_i_813_: usize,
    mut v_bs_814_: *mut leanh::LeanObject,
    mut v___y_815_: *mut leanh::LeanObject,
    mut v___y_816_: *mut leanh::LeanObject,
    mut v___y_817_: *mut leanh::LeanObject,
    mut v___y_818_: *mut leanh::LeanObject,
    mut v___y_819_: *mut leanh::LeanObject,
    mut v___y_820_: *mut leanh::LeanObject,
    mut v___y_821_: *mut leanh::LeanObject,
    mut v___y_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___redArg(v_sz_812_, v_i_813_, v_bs_814_, v___y_821_, v___y_822_);
    return v___x_824_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0___boxed(
    mut v_sz_825_: *mut leanh::LeanObject,
    mut v_i_826_: *mut leanh::LeanObject,
    mut v_bs_827_: *mut leanh::LeanObject,
    mut v___y_828_: *mut leanh::LeanObject,
    mut v___y_829_: *mut leanh::LeanObject,
    mut v___y_830_: *mut leanh::LeanObject,
    mut v___y_831_: *mut leanh::LeanObject,
    mut v___y_832_: *mut leanh::LeanObject,
    mut v___y_833_: *mut leanh::LeanObject,
    mut v___y_834_: *mut leanh::LeanObject,
    mut v___y_835_: *mut leanh::LeanObject,
    mut v___y_836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_837_: usize = 0;
    let mut v_i_boxed_838_: usize = 0;
    let mut v_res_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_837_ = leanh::lean_unbox_usize(v_sz_825_);
    leanh::lean_dec(v_sz_825_);
    v_i_boxed_838_ = leanh::lean_unbox_usize(v_i_826_);
    leanh::lean_dec(v_i_826_);
    v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalDelta_spec__0(v_sz_boxed_837_, v_i_boxed_838_, v_bs_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
    leanh::lean_dec(v___y_835_);
    leanh::lean_dec_ref(v___y_834_);
    leanh::lean_dec(v___y_833_);
    leanh::lean_dec_ref(v___y_832_);
    leanh::lean_dec(v___y_831_);
    leanh::lean_dec_ref(v___y_830_);
    leanh::lean_dec(v___y_829_);
    leanh::lean_dec_ref(v___y_828_);
    return v_res_839_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1()
-> *mut leanh::LeanObject {
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_856_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_857_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__3;
    v___x_858_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6;
    v___x_859_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalDelta___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_860_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_856_, v___x_857_, v___x_858_, v___x_859_,
    );
    return v___x_860_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___boxed(
    mut v_a_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
    return v_res_862_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3()
-> *mut leanh::LeanObject {
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6;
    v___x_866_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___closed__0;
    v___x_867_ = l_Lean_addBuiltinDocString(v___x_865_, v___x_866_);
    return v___x_867_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3___boxed(
    mut v_a_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_869_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
    return v_res_869_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5()
-> *mut leanh::LeanObject {
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1___closed__6;
    v___x_897_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___closed__6;
    v___x_898_ = l_Lean_addBuiltinDeclarationRanges(v___x_896_, v___x_897_);
    return v___x_898_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5___boxed(
    mut v_a_899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_900_ = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
    return v_res_900_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Delta(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_docString__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Delta_0__Lean_Elab_Tactic_evalDelta___regBuiltin_Lean_Elab_Tactic_evalDelta_declRange__5();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Delta(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Delta(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Delta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Delta(builtin);
}