// Lean compiler output
// Module: Lean.Elab.Tactic.ShowTerm
// Imports: Lean.Elab.ElabRules Lean.Meta.Tactic.TryThis
use crate::ffi::{lean_st_ref_get, lean_st_ref_set, lean_st_ref_take};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::ElabRules::{
    initialize_Lean_Elab_ElabRules, runtime_initialize_Lean_Elab_ElabRules,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_evalTactic, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_saveState___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType, l_Lean_Elab_Term_termElabAttribute,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_headBeta, l_Lean_mkMVar};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addExactSuggestion,
    l_Lean_Meta_Tactic_TryThis_addTermSuggestion, runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 104, 111, 119, 84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value)
            as *mut crate::leanh::LeanObject,
        6061675305592924349 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 104, 111, 119, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value) as *mut crate::leanh::LeanObject,18098057153661502739 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value) as *mut crate::leanh::LeanObject,3636147243776179156 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        115, 104, 111, 119, 84, 101, 114, 109, 69, 108, 97, 98, 73, 109, 112, 108, 0,
    ],
};
static mut l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11632085792917481440 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 83, 104, 111, 119, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value) as *mut crate::leanh::LeanObject,18098057153661502739 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value) as *mut crate::leanh::LeanObject,6342865924702849298 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [73, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 111, 102, 32, 96, 115, 104, 111, 119, 95, 116, 101, 114, 109, 96, 32, 116, 101, 114, 109, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 32, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject,((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = crate::leanh::lean_box(0);
    v___x_440_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_441_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
    crate::leanh::lean_ctor_set(v___x_441_, 1, v___x_439_);
    return v___x_441_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0);
    v___x_444_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_444_, 0, v___x_443_);
    return v___x_444_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___boxed(
    mut v___y_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_446_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
    return v_res_446_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0(
    mut v_00_u03b1_447_: *mut crate::leanh::LeanObject,
    mut v___y_448_: *mut crate::leanh::LeanObject,
    mut v___y_449_: *mut crate::leanh::LeanObject,
    mut v___y_450_: *mut crate::leanh::LeanObject,
    mut v___y_451_: *mut crate::leanh::LeanObject,
    mut v___y_452_: *mut crate::leanh::LeanObject,
    mut v___y_453_: *mut crate::leanh::LeanObject,
    mut v___y_454_: *mut crate::leanh::LeanObject,
    mut v___y_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
    return v___x_457_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___boxed(
    mut v_00_u03b1_458_: *mut crate::leanh::LeanObject,
    mut v___y_459_: *mut crate::leanh::LeanObject,
    mut v___y_460_: *mut crate::leanh::LeanObject,
    mut v___y_461_: *mut crate::leanh::LeanObject,
    mut v___y_462_: *mut crate::leanh::LeanObject,
    mut v___y_463_: *mut crate::leanh::LeanObject,
    mut v___y_464_: *mut crate::leanh::LeanObject,
    mut v___y_465_: *mut crate::leanh::LeanObject,
    mut v___y_466_: *mut crate::leanh::LeanObject,
    mut v___y_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_468_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0(
            v_00_u03b1_458_,
            v___y_459_,
            v___y_460_,
            v___y_461_,
            v___y_462_,
            v___y_463_,
            v___y_464_,
            v___y_465_,
            v___y_466_,
        );
    crate::leanh::lean_dec(v___y_466_);
    crate::leanh::lean_dec_ref(v___y_465_);
    crate::leanh::lean_dec(v___y_464_);
    crate::leanh::lean_dec_ref(v___y_463_);
    crate::leanh::lean_dec(v___y_462_);
    crate::leanh::lean_dec_ref(v___y_461_);
    crate::leanh::lean_dec(v___y_460_);
    crate::leanh::lean_dec_ref(v___y_459_);
    return v_res_468_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(
    mut v_e_469_: *mut crate::leanh::LeanObject,
    mut v___y_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_486_: u8 = 0;
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_492_: u8 = 0;
    let mut v_unused_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_472_ = l_Lean_Expr_hasMVar(v_e_469_);
                if v___x_472_ == 0 {
                    v___x_473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_473_, 0, v_e_469_);
                    return v___x_473_;
                } else {
                    v___x_474_ = lean_st_ref_get(v___y_470_);
                    v_mctx_475_ = crate::leanh::lean_ctor_get(v___x_474_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_475_);
                    crate::leanh::lean_dec(v___x_474_);
                    v___x_476_ = l_Lean_instantiateMVarsCore(v_mctx_475_, v_e_469_);
                    v_fst_477_ = crate::leanh::lean_ctor_get(v___x_476_, 0);
                    crate::leanh::lean_inc(v_fst_477_);
                    v_snd_478_ = crate::leanh::lean_ctor_get(v___x_476_, 1);
                    crate::leanh::lean_inc(v_snd_478_);
                    crate::leanh::lean_dec_ref(v___x_476_);
                    v___x_479_ = lean_st_ref_take(v___y_470_);
                    v_cache_480_ = crate::leanh::lean_ctor_get(v___x_479_, 1);
                    v_zetaDeltaFVarIds_481_ = crate::leanh::lean_ctor_get(v___x_479_, 2);
                    v_postponed_482_ = crate::leanh::lean_ctor_get(v___x_479_, 3);
                    v_diag_483_ = crate::leanh::lean_ctor_get(v___x_479_, 4);
                    v_isSharedCheck_492_ = (!crate::leanh::lean_is_exclusive(v___x_479_)) as u8;
                    if v_isSharedCheck_492_ == 0 {
                        v_unused_493_ = crate::leanh::lean_ctor_get(v___x_479_, 0);
                        crate::leanh::lean_dec(v_unused_493_);
                        v___x_485_ = v___x_479_;
                        v_isShared_486_ = v_isSharedCheck_492_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_483_);
                        crate::leanh::lean_inc(v_postponed_482_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_481_);
                        crate::leanh::lean_inc(v_cache_480_);
                        crate::leanh::lean_dec(v___x_479_);
                        v___x_485_ = crate::leanh::lean_box(0);
                        v_isShared_486_ = v_isSharedCheck_492_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_486_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_485_, 0, v_snd_478_);
                    v___x_488_ = v___x_485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_491_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_491_, 0, v_snd_478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_491_, 1, v_cache_480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_491_, 2, v_zetaDeltaFVarIds_481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_491_, 3, v_postponed_482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_491_, 4, v_diag_483_);
                    v___x_488_ = v_reuseFailAlloc_491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_489_ = lean_st_ref_set(v___y_470_, v___x_488_);
                v___x_490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_490_, 0, v_fst_477_);
                return v___x_490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg___boxed(
    mut v_e_494_: *mut crate::leanh::LeanObject,
    mut v___y_495_: *mut crate::leanh::LeanObject,
    mut v___y_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_497_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(
            v_e_494_, v___y_495_,
        );
    crate::leanh::lean_dec(v___y_495_);
    return v_res_497_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1(
    mut v_e_498_: *mut crate::leanh::LeanObject,
    mut v___y_499_: *mut crate::leanh::LeanObject,
    mut v___y_500_: *mut crate::leanh::LeanObject,
    mut v___y_501_: *mut crate::leanh::LeanObject,
    mut v___y_502_: *mut crate::leanh::LeanObject,
    mut v___y_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
    mut v___y_505_: *mut crate::leanh::LeanObject,
    mut v___y_506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_508_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(
            v_e_498_, v___y_504_,
        );
    return v___x_508_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___boxed(
    mut v_e_509_: *mut crate::leanh::LeanObject,
    mut v___y_510_: *mut crate::leanh::LeanObject,
    mut v___y_511_: *mut crate::leanh::LeanObject,
    mut v___y_512_: *mut crate::leanh::LeanObject,
    mut v___y_513_: *mut crate::leanh::LeanObject,
    mut v___y_514_: *mut crate::leanh::LeanObject,
    mut v___y_515_: *mut crate::leanh::LeanObject,
    mut v___y_516_: *mut crate::leanh::LeanObject,
    mut v___y_517_: *mut crate::leanh::LeanObject,
    mut v___y_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1(
        v_e_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_,
        v___y_516_, v___y_517_,
    );
    crate::leanh::lean_dec(v___y_517_);
    crate::leanh::lean_dec_ref(v___y_516_);
    crate::leanh::lean_dec(v___y_515_);
    crate::leanh::lean_dec_ref(v___y_514_);
    crate::leanh::lean_dec(v___y_513_);
    crate::leanh::lean_dec_ref(v___y_512_);
    crate::leanh::lean_dec(v___y_511_);
    crate::leanh::lean_dec_ref(v___y_510_);
    return v_res_519_;
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0(
    mut v___x_520_: *mut crate::leanh::LeanObject,
    mut v_tk_521_: *mut crate::leanh::LeanObject,
    mut v___x_522_: u8,
    mut v___y_523_: *mut crate::leanh::LeanObject,
    mut v___y_524_: *mut crate::leanh::LeanObject,
    mut v___y_525_: *mut crate::leanh::LeanObject,
    mut v___y_526_: *mut crate::leanh::LeanObject,
    mut v___y_527_: *mut crate::leanh::LeanObject,
    mut v___y_528_: *mut crate::leanh::LeanObject,
    mut v___y_529_: *mut crate::leanh::LeanObject,
    mut v___y_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_539_: u8 = 0;
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_545_: u8 = 0;
    let mut v_ref_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_isSharedCheck_558_: u8 = 0;
    let mut v_unused_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_563_: u8 = 0;
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut v_a_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_571_: u8 = 0;
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_532_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_524_, v___y_527_, v___y_528_, v___y_529_, v___y_530_,
                );
                if crate::leanh::lean_obj_tag(v___x_532_) == 0 {
                    v_a_533_ = crate::leanh::lean_ctor_get(v___x_532_, 0);
                    crate::leanh::lean_inc(v_a_533_);
                    crate::leanh::lean_dec_ref_known(v___x_532_, 1);
                    v___x_534_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_524_, v___y_526_, v___y_528_, v___y_530_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_534_) == 0 {
                        v_a_535_ = crate::leanh::lean_ctor_get(v___x_534_, 0);
                        crate::leanh::lean_inc(v_a_535_);
                        crate::leanh::lean_dec_ref_known(v___x_534_, 1);
                        v___x_536_ = l_Lean_Elab_Tactic_evalTactic(
                            v___x_520_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_,
                            v___y_528_, v___y_529_, v___y_530_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_536_) == 0 {
                            v_isSharedCheck_558_ =
                                (!crate::leanh::lean_is_exclusive(v___x_536_)) as u8;
                            if v_isSharedCheck_558_ == 0 {
                                v_unused_559_ = crate::leanh::lean_ctor_get(v___x_536_, 0);
                                crate::leanh::lean_dec(v_unused_559_);
                                v___x_538_ = v___x_536_;
                                v_isShared_539_ = v_isSharedCheck_558_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_536_);
                                v___x_538_ = crate::leanh::lean_box(0);
                                v_isShared_539_ = v_isSharedCheck_558_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_535_);
                            crate::leanh::lean_dec(v_a_533_);
                            crate::leanh::lean_dec(v_tk_521_);
                            return v___x_536_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_533_);
                        crate::leanh::lean_dec(v_tk_521_);
                        crate::leanh::lean_dec(v___x_520_);
                        v_a_560_ = crate::leanh::lean_ctor_get(v___x_534_, 0);
                        v_isSharedCheck_567_ = (!crate::leanh::lean_is_exclusive(v___x_534_)) as u8;
                        if v_isSharedCheck_567_ == 0 {
                            v___x_562_ = v___x_534_;
                            v_isShared_563_ = v_isSharedCheck_567_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_560_);
                            crate::leanh::lean_dec(v___x_534_);
                            v___x_562_ = crate::leanh::lean_box(0);
                            v_isShared_563_ = v_isSharedCheck_567_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_tk_521_);
                    crate::leanh::lean_dec(v___x_520_);
                    v_a_568_ = crate::leanh::lean_ctor_get(v___x_532_, 0);
                    v_isSharedCheck_575_ = (!crate::leanh::lean_is_exclusive(v___x_532_)) as u8;
                    if v_isSharedCheck_575_ == 0 {
                        v___x_570_ = v___x_532_;
                        v_isShared_571_ = v_isSharedCheck_575_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_568_);
                        crate::leanh::lean_dec(v___x_532_);
                        v___x_570_ = crate::leanh::lean_box(0);
                        v_isShared_571_ = v_isSharedCheck_575_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_540_ = l_Lean_mkMVar(v_a_533_);
                v___x_541_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(v___x_540_, v___y_528_);
                v_a_542_ = crate::leanh::lean_ctor_get(v___x_541_, 0);
                v_isSharedCheck_557_ = (!crate::leanh::lean_is_exclusive(v___x_541_)) as u8;
                if v_isSharedCheck_557_ == 0 {
                    v___x_544_ = v___x_541_;
                    v_isShared_545_ = v_isSharedCheck_557_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_542_);
                    crate::leanh::lean_dec(v___x_541_);
                    v___x_544_ = crate::leanh::lean_box(0);
                    v_isShared_545_ = v_isSharedCheck_557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_ref_546_ = crate::leanh::lean_ctor_get(v___y_529_, 5);
                v___x_547_ = l_Lean_Expr_headBeta(v_a_542_);
                crate::leanh::lean_inc(v_ref_546_);
                if v_isShared_545_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_544_, 1);
                    crate::leanh::lean_ctor_set(v___x_544_, 0, v_ref_546_);
                    v___x_549_ = v___x_544_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_556_, 0, v_ref_546_);
                    v___x_549_ = v_reuseFailAlloc_556_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_550_ = 0;
                v___x_551_ = crate::leanh::lean_box(0);
                if v_isShared_539_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_538_, 1);
                    crate::leanh::lean_ctor_set(v___x_538_, 0, v_a_535_);
                    v___x_553_ = v___x_538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_535_);
                    v___x_553_ = v_reuseFailAlloc_555_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_554_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(
                    v_tk_521_, v___x_547_, v___x_549_, v___x_550_, v___x_551_, v___x_553_,
                    v___x_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_,
                    v___y_528_, v___y_529_, v___y_530_,
                );
                return v___x_554_;
            }
            5 => {
                if v_isShared_563_ == 0 {
                    v___x_565_ = v___x_562_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_566_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
                    v___x_565_ = v_reuseFailAlloc_566_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_565_;
            }
            7 => {
                if v_isShared_571_ == 0 {
                    v___x_573_ = v___x_570_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
                    v___x_573_ = v_reuseFailAlloc_574_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0___boxed(
    mut v___x_576_: *mut crate::leanh::LeanObject,
    mut v_tk_577_: *mut crate::leanh::LeanObject,
    mut v___x_578_: *mut crate::leanh::LeanObject,
    mut v___y_579_: *mut crate::leanh::LeanObject,
    mut v___y_580_: *mut crate::leanh::LeanObject,
    mut v___y_581_: *mut crate::leanh::LeanObject,
    mut v___y_582_: *mut crate::leanh::LeanObject,
    mut v___y_583_: *mut crate::leanh::LeanObject,
    mut v___y_584_: *mut crate::leanh::LeanObject,
    mut v___y_585_: *mut crate::leanh::LeanObject,
    mut v___y_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2252__boxed_588_: u8 = 0;
    let mut v_res_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252__boxed_588_ = (crate::leanh::lean_unbox(v___x_578_) as u8);
    v_res_589_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0(
        v___x_576_,
        v_tk_577_,
        v___x_2252__boxed_588_,
        v___y_579_,
        v___y_580_,
        v___y_581_,
        v___y_582_,
        v___y_583_,
        v___y_584_,
        v___y_585_,
        v___y_586_,
    );
    crate::leanh::lean_dec(v___y_586_);
    crate::leanh::lean_dec_ref(v___y_585_);
    crate::leanh::lean_dec(v___y_584_);
    crate::leanh::lean_dec_ref(v___y_583_);
    crate::leanh::lean_dec(v___y_582_);
    crate::leanh::lean_dec_ref(v___y_581_);
    crate::leanh::lean_dec(v___y_580_);
    crate::leanh::lean_dec_ref(v___y_579_);
    return v_res_589_;
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_evalShowTerm(
    mut v_stx_599_: *mut crate::leanh::LeanObject,
    mut v_a_600_: *mut crate::leanh::LeanObject,
    mut v_a_601_: *mut crate::leanh::LeanObject,
    mut v_a_602_: *mut crate::leanh::LeanObject,
    mut v_a_603_: *mut crate::leanh::LeanObject,
    mut v_a_604_: *mut crate::leanh::LeanObject,
    mut v_a_605_: *mut crate::leanh::LeanObject,
    mut v_a_606_: *mut crate::leanh::LeanObject,
    mut v_a_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    v___x_609_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4;
    crate::leanh::lean_inc(v_stx_599_);
    v___x_610_ = l_Lean_Syntax_isOfKind(v_stx_599_, v___x_609_);
    if v___x_610_ == 0 {
        let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_599_);
        v___x_611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
        return v___x_611_;
    } else {
        let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_612_ = crate::leanh::lean_unsigned_to_nat(0);
        v_tk_613_ = l_Lean_Syntax_getArg(v_stx_599_, v___x_612_);
        v___x_614_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_615_ = l_Lean_Syntax_getArg(v_stx_599_, v___x_614_);
        crate::leanh::lean_dec(v_stx_599_);
        v___x_616_ = crate::leanh::lean_box((v___x_610_) as usize);
        v___f_617_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0___boxed as *mut core::ffi::c_void,
            12,
            3,
        );
        crate::leanh::lean_closure_set(v___f_617_, 0, v___x_615_);
        crate::leanh::lean_closure_set(v___f_617_, 1, v_tk_613_);
        crate::leanh::lean_closure_set(v___f_617_, 2, v___x_616_);
        v___x_618_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_617_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_,
            v_a_607_,
        );
        return v___x_618_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___boxed(
    mut v_stx_619_: *mut crate::leanh::LeanObject,
    mut v_a_620_: *mut crate::leanh::LeanObject,
    mut v_a_621_: *mut crate::leanh::LeanObject,
    mut v_a_622_: *mut crate::leanh::LeanObject,
    mut v_a_623_: *mut crate::leanh::LeanObject,
    mut v_a_624_: *mut crate::leanh::LeanObject,
    mut v_a_625_: *mut crate::leanh::LeanObject,
    mut v_a_626_: *mut crate::leanh::LeanObject,
    mut v_a_627_: *mut crate::leanh::LeanObject,
    mut v_a_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm(
        v_stx_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_,
    );
    crate::leanh::lean_dec(v_a_627_);
    crate::leanh::lean_dec_ref(v_a_626_);
    crate::leanh::lean_dec(v_a_625_);
    crate::leanh::lean_dec_ref(v_a_624_);
    crate::leanh::lean_dec(v_a_623_);
    crate::leanh::lean_dec_ref(v_a_622_);
    crate::leanh::lean_dec(v_a_621_);
    crate::leanh::lean_dec_ref(v_a_620_);
    return v_res_629_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_641_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4;
    v___x_642_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3;
    v___x_643_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_644_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_640_, v___x_641_, v___x_642_, v___x_643_,
    );
    return v___x_644_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___boxed(
    mut v_a_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1();
    return v_res_646_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3;
    v___x_674_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6;
    v___x_675_ = l_Lean_addBuiltinDeclarationRanges(v___x_673_, v___x_674_);
    return v___x_675_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___boxed(
    mut v_a_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3();
    return v_res_677_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0);
    v___x_680_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_680_, 0, v___x_679_);
    return v___x_680_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg___boxed(
    mut v___y_681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_682_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
    return v_res_682_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0(
    mut v_00_u03b1_683_: *mut crate::leanh::LeanObject,
    mut v___y_684_: *mut crate::leanh::LeanObject,
    mut v___y_685_: *mut crate::leanh::LeanObject,
    mut v___y_686_: *mut crate::leanh::LeanObject,
    mut v___y_687_: *mut crate::leanh::LeanObject,
    mut v___y_688_: *mut crate::leanh::LeanObject,
    mut v___y_689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
    return v___x_691_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___boxed(
    mut v_00_u03b1_692_: *mut crate::leanh::LeanObject,
    mut v___y_693_: *mut crate::leanh::LeanObject,
    mut v___y_694_: *mut crate::leanh::LeanObject,
    mut v___y_695_: *mut crate::leanh::LeanObject,
    mut v___y_696_: *mut crate::leanh::LeanObject,
    mut v___y_697_: *mut crate::leanh::LeanObject,
    mut v___y_698_: *mut crate::leanh::LeanObject,
    mut v___y_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_700_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0(
            v_00_u03b1_692_,
            v___y_693_,
            v___y_694_,
            v___y_695_,
            v___y_696_,
            v___y_697_,
            v___y_698_,
        );
    crate::leanh::lean_dec(v___y_698_);
    crate::leanh::lean_dec_ref(v___y_697_);
    crate::leanh::lean_dec(v___y_696_);
    crate::leanh::lean_dec_ref(v___y_695_);
    crate::leanh::lean_dec(v___y_694_);
    crate::leanh::lean_dec_ref(v___y_693_);
    return v_res_700_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(
    mut v_e_701_: *mut crate::leanh::LeanObject,
    mut v___y_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_718_: u8 = 0;
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut v_unused_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_704_ = l_Lean_Expr_hasMVar(v_e_701_);
                if v___x_704_ == 0 {
                    v___x_705_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_705_, 0, v_e_701_);
                    return v___x_705_;
                } else {
                    v___x_706_ = lean_st_ref_get(v___y_702_);
                    v_mctx_707_ = crate::leanh::lean_ctor_get(v___x_706_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_707_);
                    crate::leanh::lean_dec(v___x_706_);
                    v___x_708_ = l_Lean_instantiateMVarsCore(v_mctx_707_, v_e_701_);
                    v_fst_709_ = crate::leanh::lean_ctor_get(v___x_708_, 0);
                    crate::leanh::lean_inc(v_fst_709_);
                    v_snd_710_ = crate::leanh::lean_ctor_get(v___x_708_, 1);
                    crate::leanh::lean_inc(v_snd_710_);
                    crate::leanh::lean_dec_ref(v___x_708_);
                    v___x_711_ = lean_st_ref_take(v___y_702_);
                    v_cache_712_ = crate::leanh::lean_ctor_get(v___x_711_, 1);
                    v_zetaDeltaFVarIds_713_ = crate::leanh::lean_ctor_get(v___x_711_, 2);
                    v_postponed_714_ = crate::leanh::lean_ctor_get(v___x_711_, 3);
                    v_diag_715_ = crate::leanh::lean_ctor_get(v___x_711_, 4);
                    v_isSharedCheck_724_ = (!crate::leanh::lean_is_exclusive(v___x_711_)) as u8;
                    if v_isSharedCheck_724_ == 0 {
                        v_unused_725_ = crate::leanh::lean_ctor_get(v___x_711_, 0);
                        crate::leanh::lean_dec(v_unused_725_);
                        v___x_717_ = v___x_711_;
                        v_isShared_718_ = v_isSharedCheck_724_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_715_);
                        crate::leanh::lean_inc(v_postponed_714_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_713_);
                        crate::leanh::lean_inc(v_cache_712_);
                        crate::leanh::lean_dec(v___x_711_);
                        v___x_717_ = crate::leanh::lean_box(0);
                        v_isShared_718_ = v_isSharedCheck_724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_718_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_717_, 0, v_snd_710_);
                    v___x_720_ = v___x_717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_723_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 0, v_snd_710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 1, v_cache_712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 2, v_zetaDeltaFVarIds_713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 3, v_postponed_714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_723_, 4, v_diag_715_);
                    v___x_720_ = v_reuseFailAlloc_723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_721_ = lean_st_ref_set(v___y_702_, v___x_720_);
                v___x_722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_722_, 0, v_fst_709_);
                return v___x_722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg___boxed(
    mut v_e_726_: *mut crate::leanh::LeanObject,
    mut v___y_727_: *mut crate::leanh::LeanObject,
    mut v___y_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(
            v_e_726_, v___y_727_,
        );
    crate::leanh::lean_dec(v___y_727_);
    return v_res_729_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1(
    mut v_e_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(
            v_e_730_, v___y_734_,
        );
    return v___x_738_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___boxed(
    mut v_e_739_: *mut crate::leanh::LeanObject,
    mut v___y_740_: *mut crate::leanh::LeanObject,
    mut v___y_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_747_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1(
        v_e_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_,
    );
    crate::leanh::lean_dec(v___y_745_);
    crate::leanh::lean_dec_ref(v___y_744_);
    crate::leanh::lean_dec(v___y_743_);
    crate::leanh::lean_dec_ref(v___y_742_);
    crate::leanh::lean_dec(v___y_741_);
    crate::leanh::lean_dec_ref(v___y_740_);
    return v_res_747_;
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_elabShowTerm(
    mut v_x_756_: *mut crate::leanh::LeanObject,
    mut v_x_757_: *mut crate::leanh::LeanObject,
    mut v_a_758_: *mut crate::leanh::LeanObject,
    mut v_a_759_: *mut crate::leanh::LeanObject,
    mut v_a_760_: *mut crate::leanh::LeanObject,
    mut v_a_761_: *mut crate::leanh::LeanObject,
    mut v_a_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: u8 = 0;
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_779_: u8 = 0;
    let mut v_ref_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut v_unused_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut v_reuseFailAlloc_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut v_a_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_809_: u8 = 0;
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_765_ = l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2;
                crate::leanh::lean_inc(v_x_756_);
                v___x_766_ = l_Lean_Syntax_isOfKind(v_x_756_, v___x_765_);
                if v___x_766_ == 0 {
                    crate::leanh::lean_dec(v_x_757_);
                    crate::leanh::lean_dec(v_x_756_);
                    v___x_767_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
                    return v___x_767_;
                } else {
                    v___x_768_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_769_ = l_Lean_Syntax_getArg(v_x_756_, v___x_768_);
                    v___x_770_ = crate::leanh::lean_box(0);
                    v___x_771_ = l_Lean_Elab_Term_elabTermEnsuringType(
                        v___x_769_, v_x_757_, v___x_766_, v___x_766_, v___x_770_, v_a_758_,
                        v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_771_) == 0 {
                        v_a_772_ = crate::leanh::lean_ctor_get(v___x_771_, 0);
                        crate::leanh::lean_inc(v_a_772_);
                        crate::leanh::lean_dec_ref_known(v___x_771_, 1);
                        v___x_773_ = 0;
                        v___x_774_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                            v___x_773_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_774_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_774_, 1);
                            crate::leanh::lean_inc(v_a_772_);
                            v___x_775_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(v_a_772_, v_a_761_);
                            v_a_776_ = crate::leanh::lean_ctor_get(v___x_775_, 0);
                            v_isSharedCheck_805_ =
                                (!crate::leanh::lean_is_exclusive(v___x_775_)) as u8;
                            if v_isSharedCheck_805_ == 0 {
                                v___x_778_ = v___x_775_;
                                v_isShared_779_ = v_isSharedCheck_805_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_776_);
                                crate::leanh::lean_dec(v___x_775_);
                                v___x_778_ = crate::leanh::lean_box(0);
                                v_isShared_779_ = v_isSharedCheck_805_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_772_);
                            crate::leanh::lean_dec(v_x_756_);
                            v_a_806_ = crate::leanh::lean_ctor_get(v___x_774_, 0);
                            v_isSharedCheck_813_ =
                                (!crate::leanh::lean_is_exclusive(v___x_774_)) as u8;
                            if v_isSharedCheck_813_ == 0 {
                                v___x_808_ = v___x_774_;
                                v_isShared_809_ = v_isSharedCheck_813_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_806_);
                                crate::leanh::lean_dec(v___x_774_);
                                v___x_808_ = crate::leanh::lean_box(0);
                                v_isShared_809_ = v_isSharedCheck_813_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_756_);
                        return v___x_771_;
                    }
                }
            }
            1 => {
                v_ref_780_ = crate::leanh::lean_ctor_get(v_a_762_, 5);
                v___x_781_ = crate::leanh::lean_unsigned_to_nat(0);
                v_tk_782_ = l_Lean_Syntax_getArg(v_x_756_, v___x_781_);
                crate::leanh::lean_dec(v_x_756_);
                v___x_783_ = l_Lean_Expr_headBeta(v_a_776_);
                crate::leanh::lean_inc(v_ref_780_);
                if v_isShared_779_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_778_, 1);
                    crate::leanh::lean_ctor_set(v___x_778_, 0, v_ref_780_);
                    v___x_785_ = v___x_778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v_ref_780_);
                    v___x_785_ = v_reuseFailAlloc_804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_786_ = l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3;
                v___x_787_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(
                    v_tk_782_, v___x_783_, v___x_785_, v___x_786_, v___x_770_, v_a_760_, v_a_761_,
                    v_a_762_, v_a_763_,
                );
                if crate::leanh::lean_obj_tag(v___x_787_) == 0 {
                    v_isSharedCheck_794_ = (!crate::leanh::lean_is_exclusive(v___x_787_)) as u8;
                    if v_isSharedCheck_794_ == 0 {
                        v_unused_795_ = crate::leanh::lean_ctor_get(v___x_787_, 0);
                        crate::leanh::lean_dec(v_unused_795_);
                        v___x_789_ = v___x_787_;
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_787_);
                        v___x_789_ = crate::leanh::lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_772_);
                    v_a_796_ = crate::leanh::lean_ctor_get(v___x_787_, 0);
                    v_isSharedCheck_803_ = (!crate::leanh::lean_is_exclusive(v___x_787_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_798_ = v___x_787_;
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_796_);
                        crate::leanh::lean_dec(v___x_787_);
                        v___x_798_ = crate::leanh::lean_box(0);
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_790_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_789_, 0, v_a_772_);
                    v___x_792_ = v___x_789_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_772_);
                    v___x_792_ = v_reuseFailAlloc_793_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_792_;
            }
            5 => {
                if v_isShared_799_ == 0 {
                    v___x_801_ = v___x_798_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
                    v___x_801_ = v_reuseFailAlloc_802_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_801_;
            }
            7 => {
                if v_isShared_809_ == 0 {
                    v___x_811_ = v___x_808_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_812_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
                    v___x_811_ = v_reuseFailAlloc_812_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___boxed(
    mut v_x_814_: *mut crate::leanh::LeanObject,
    mut v_x_815_: *mut crate::leanh::LeanObject,
    mut v_a_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
    mut v_a_818_: *mut crate::leanh::LeanObject,
    mut v_a_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Lean_Elab_Tactic_ShowTerm_elabShowTerm(
        v_x_814_, v_x_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_,
    );
    crate::leanh::lean_dec(v_a_821_);
    crate::leanh::lean_dec_ref(v_a_820_);
    crate::leanh::lean_dec(v_a_819_);
    crate::leanh::lean_dec_ref(v_a_818_);
    crate::leanh::lean_dec(v_a_817_);
    crate::leanh::lean_dec_ref(v_a_816_);
    return v_res_823_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_833_ = l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2;
    v___x_834_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1;
    v___x_835_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_836_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_832_, v___x_833_, v___x_834_, v___x_835_,
    );
    return v___x_836_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___boxed(
    mut v_a_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1();
    return v_res_838_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_841_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1;
    v___x_842_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0;
    v___x_843_ = l_Lean_addBuiltinDocString(v___x_841_, v___x_842_);
    return v___x_843_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___boxed(
    mut v_a_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3();
    return v_res_845_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1;
    v___x_873_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6;
    v___x_874_ = l_Lean_addBuiltinDeclarationRanges(v___x_872_, v___x_873_);
    return v___x_874_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___boxed(
    mut v_a_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_876_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5();
    return v_res_876_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_ShowTerm(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ElabRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_ShowTerm(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_ShowTerm(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ElabRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ShowTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_ShowTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_ShowTerm(builtin);
}
