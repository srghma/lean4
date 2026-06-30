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
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value:
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
    m_data: [115, 104, 111, 119, 84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__3_value)
            as *mut leanh::LeanObject,
        6061675305592924349 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 104, 111, 119, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value) as *mut leanh::LeanObject,18098057153661502739 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__2_value) as *mut leanh::LeanObject,3636147243776179156 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__0_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__1_value)
            as *mut leanh::LeanObject,
        11632085792917481440 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3_value:
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
    m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0],
};
static mut l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 83, 104, 111, 119, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__1_value) as *mut leanh::LeanObject,18098057153661502739 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__0_value) as *mut leanh::LeanObject,6342865924702849298 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0_value: leanh::LeanStringObject<48> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [73, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 111, 102, 32, 96, 115, 104, 111, 119, 95, 116, 101, 114, 109, 96, 32, 116, 101, 114, 109, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 32, 0]};
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 38 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__0_value) as *mut leanh::LeanObject,((( 38 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__1_value) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__3_value) as *mut leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__4_value) as *mut leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = leanh::lean_box(0);
    v___x_440_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_441_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
    leanh::lean_ctor_set(v___x_441_, 1, v___x_439_);
    return v___x_441_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0);
    v___x_444_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_444_, 0, v___x_443_);
    return v___x_444_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___boxed(
    mut v___y_445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_446_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
    return v_res_446_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0(
    mut v_00_u03b1_447_: *mut leanh::LeanObject,
    mut v___y_448_: *mut leanh::LeanObject,
    mut v___y_449_: *mut leanh::LeanObject,
    mut v___y_450_: *mut leanh::LeanObject,
    mut v___y_451_: *mut leanh::LeanObject,
    mut v___y_452_: *mut leanh::LeanObject,
    mut v___y_453_: *mut leanh::LeanObject,
    mut v___y_454_: *mut leanh::LeanObject,
    mut v___y_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
    return v___x_457_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___boxed(
    mut v_00_u03b1_458_: *mut leanh::LeanObject,
    mut v___y_459_: *mut leanh::LeanObject,
    mut v___y_460_: *mut leanh::LeanObject,
    mut v___y_461_: *mut leanh::LeanObject,
    mut v___y_462_: *mut leanh::LeanObject,
    mut v___y_463_: *mut leanh::LeanObject,
    mut v___y_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
    mut v___y_467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_468_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_466_);
    leanh::lean_dec_ref(v___y_465_);
    leanh::lean_dec(v___y_464_);
    leanh::lean_dec_ref(v___y_463_);
    leanh::lean_dec(v___y_462_);
    leanh::lean_dec_ref(v___y_461_);
    leanh::lean_dec(v___y_460_);
    leanh::lean_dec_ref(v___y_459_);
    return v_res_468_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(
    mut v_e_469_: *mut leanh::LeanObject,
    mut v___y_470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_472_: u8 = 0;
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_486_: u8 = 0;
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_492_: u8 = 0;
    let mut v_unused_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_472_ = l_Lean_Expr_hasMVar(v_e_469_);
                if v___x_472_ == 0 {
                    v___x_473_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_473_, 0, v_e_469_);
                    return v___x_473_;
                } else {
                    v___x_474_ = lean_st_ref_get(v___y_470_);
                    v_mctx_475_ = leanh::lean_ctor_get(v___x_474_, 0);
                    leanh::lean_inc_ref(v_mctx_475_);
                    leanh::lean_dec(v___x_474_);
                    v___x_476_ = l_Lean_instantiateMVarsCore(v_mctx_475_, v_e_469_);
                    v_fst_477_ = leanh::lean_ctor_get(v___x_476_, 0);
                    leanh::lean_inc(v_fst_477_);
                    v_snd_478_ = leanh::lean_ctor_get(v___x_476_, 1);
                    leanh::lean_inc(v_snd_478_);
                    leanh::lean_dec_ref(v___x_476_);
                    v___x_479_ = lean_st_ref_take(v___y_470_);
                    v_cache_480_ = leanh::lean_ctor_get(v___x_479_, 1);
                    v_zetaDeltaFVarIds_481_ = leanh::lean_ctor_get(v___x_479_, 2);
                    v_postponed_482_ = leanh::lean_ctor_get(v___x_479_, 3);
                    v_diag_483_ = leanh::lean_ctor_get(v___x_479_, 4);
                    v_isSharedCheck_492_ = (!leanh::lean_is_exclusive(v___x_479_)) as u8;
                    if v_isSharedCheck_492_ == 0 {
                        v_unused_493_ = leanh::lean_ctor_get(v___x_479_, 0);
                        leanh::lean_dec(v_unused_493_);
                        v___x_485_ = v___x_479_;
                        v_isShared_486_ = v_isSharedCheck_492_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_483_);
                        leanh::lean_inc(v_postponed_482_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_481_);
                        leanh::lean_inc(v_cache_480_);
                        leanh::lean_dec(v___x_479_);
                        v___x_485_ = leanh::lean_box(0);
                        v_isShared_486_ = v_isSharedCheck_492_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_486_ == 0 {
                    leanh::lean_ctor_set(v___x_485_, 0, v_snd_478_);
                    v___x_488_ = v___x_485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_491_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_491_, 0, v_snd_478_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_491_, 1, v_cache_480_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_491_, 2, v_zetaDeltaFVarIds_481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_491_, 3, v_postponed_482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_491_, 4, v_diag_483_);
                    v___x_488_ = v_reuseFailAlloc_491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_489_ = lean_st_ref_set(v___y_470_, v___x_488_);
                v___x_490_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_490_, 0, v_fst_477_);
                return v___x_490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg___boxed(
    mut v_e_494_: *mut leanh::LeanObject,
    mut v___y_495_: *mut leanh::LeanObject,
    mut v___y_496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_497_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(
            v_e_494_, v___y_495_,
        );
    leanh::lean_dec(v___y_495_);
    return v_res_497_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1(
    mut v_e_498_: *mut leanh::LeanObject,
    mut v___y_499_: *mut leanh::LeanObject,
    mut v___y_500_: *mut leanh::LeanObject,
    mut v___y_501_: *mut leanh::LeanObject,
    mut v___y_502_: *mut leanh::LeanObject,
    mut v___y_503_: *mut leanh::LeanObject,
    mut v___y_504_: *mut leanh::LeanObject,
    mut v___y_505_: *mut leanh::LeanObject,
    mut v___y_506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_508_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(
            v_e_498_, v___y_504_,
        );
    return v___x_508_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___boxed(
    mut v_e_509_: *mut leanh::LeanObject,
    mut v___y_510_: *mut leanh::LeanObject,
    mut v___y_511_: *mut leanh::LeanObject,
    mut v___y_512_: *mut leanh::LeanObject,
    mut v___y_513_: *mut leanh::LeanObject,
    mut v___y_514_: *mut leanh::LeanObject,
    mut v___y_515_: *mut leanh::LeanObject,
    mut v___y_516_: *mut leanh::LeanObject,
    mut v___y_517_: *mut leanh::LeanObject,
    mut v___y_518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1(
        v_e_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_,
        v___y_516_, v___y_517_,
    );
    leanh::lean_dec(v___y_517_);
    leanh::lean_dec_ref(v___y_516_);
    leanh::lean_dec(v___y_515_);
    leanh::lean_dec_ref(v___y_514_);
    leanh::lean_dec(v___y_513_);
    leanh::lean_dec_ref(v___y_512_);
    leanh::lean_dec(v___y_511_);
    leanh::lean_dec_ref(v___y_510_);
    return v_res_519_;
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0(
    mut v___x_520_: *mut leanh::LeanObject,
    mut v_tk_521_: *mut leanh::LeanObject,
    mut v___x_522_: u8,
    mut v___y_523_: *mut leanh::LeanObject,
    mut v___y_524_: *mut leanh::LeanObject,
    mut v___y_525_: *mut leanh::LeanObject,
    mut v___y_526_: *mut leanh::LeanObject,
    mut v___y_527_: *mut leanh::LeanObject,
    mut v___y_528_: *mut leanh::LeanObject,
    mut v___y_529_: *mut leanh::LeanObject,
    mut v___y_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_539_: u8 = 0;
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_545_: u8 = 0;
    let mut v_ref_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_isSharedCheck_558_: u8 = 0;
    let mut v_unused_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_563_: u8 = 0;
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut v_a_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_571_: u8 = 0;
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_532_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_524_, v___y_527_, v___y_528_, v___y_529_, v___y_530_,
                );
                if leanh::lean_obj_tag(v___x_532_) == 0 {
                    v_a_533_ = leanh::lean_ctor_get(v___x_532_, 0);
                    leanh::lean_inc(v_a_533_);
                    leanh::lean_dec_ref_known(v___x_532_, 1);
                    v___x_534_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_524_, v___y_526_, v___y_528_, v___y_530_,
                    );
                    if leanh::lean_obj_tag(v___x_534_) == 0 {
                        v_a_535_ = leanh::lean_ctor_get(v___x_534_, 0);
                        leanh::lean_inc(v_a_535_);
                        leanh::lean_dec_ref_known(v___x_534_, 1);
                        v___x_536_ = l_Lean_Elab_Tactic_evalTactic(
                            v___x_520_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_,
                            v___y_528_, v___y_529_, v___y_530_,
                        );
                        if leanh::lean_obj_tag(v___x_536_) == 0 {
                            v_isSharedCheck_558_ =
                                (!leanh::lean_is_exclusive(v___x_536_)) as u8;
                            if v_isSharedCheck_558_ == 0 {
                                v_unused_559_ = leanh::lean_ctor_get(v___x_536_, 0);
                                leanh::lean_dec(v_unused_559_);
                                v___x_538_ = v___x_536_;
                                v_isShared_539_ = v_isSharedCheck_558_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_536_);
                                v___x_538_ = leanh::lean_box(0);
                                v_isShared_539_ = v_isSharedCheck_558_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_535_);
                            leanh::lean_dec(v_a_533_);
                            leanh::lean_dec(v_tk_521_);
                            return v___x_536_;
                        }
                    } else {
                        leanh::lean_dec(v_a_533_);
                        leanh::lean_dec(v_tk_521_);
                        leanh::lean_dec(v___x_520_);
                        v_a_560_ = leanh::lean_ctor_get(v___x_534_, 0);
                        v_isSharedCheck_567_ = (!leanh::lean_is_exclusive(v___x_534_)) as u8;
                        if v_isSharedCheck_567_ == 0 {
                            v___x_562_ = v___x_534_;
                            v_isShared_563_ = v_isSharedCheck_567_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_560_);
                            leanh::lean_dec(v___x_534_);
                            v___x_562_ = leanh::lean_box(0);
                            v_isShared_563_ = v_isSharedCheck_567_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_tk_521_);
                    leanh::lean_dec(v___x_520_);
                    v_a_568_ = leanh::lean_ctor_get(v___x_532_, 0);
                    v_isSharedCheck_575_ = (!leanh::lean_is_exclusive(v___x_532_)) as u8;
                    if v_isSharedCheck_575_ == 0 {
                        v___x_570_ = v___x_532_;
                        v_isShared_571_ = v_isSharedCheck_575_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_568_);
                        leanh::lean_dec(v___x_532_);
                        v___x_570_ = leanh::lean_box(0);
                        v_isShared_571_ = v_isSharedCheck_575_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_540_ = l_Lean_mkMVar(v_a_533_);
                v___x_541_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__1___redArg(v___x_540_, v___y_528_);
                v_a_542_ = leanh::lean_ctor_get(v___x_541_, 0);
                v_isSharedCheck_557_ = (!leanh::lean_is_exclusive(v___x_541_)) as u8;
                if v_isSharedCheck_557_ == 0 {
                    v___x_544_ = v___x_541_;
                    v_isShared_545_ = v_isSharedCheck_557_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_542_);
                    leanh::lean_dec(v___x_541_);
                    v___x_544_ = leanh::lean_box(0);
                    v_isShared_545_ = v_isSharedCheck_557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_ref_546_ = leanh::lean_ctor_get(v___y_529_, 5);
                v___x_547_ = l_Lean_Expr_headBeta(v_a_542_);
                leanh::lean_inc(v_ref_546_);
                if v_isShared_545_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_544_, 1);
                    leanh::lean_ctor_set(v___x_544_, 0, v_ref_546_);
                    v___x_549_ = v___x_544_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_556_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_556_, 0, v_ref_546_);
                    v___x_549_ = v_reuseFailAlloc_556_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_550_ = 0;
                v___x_551_ = leanh::lean_box(0);
                if v_isShared_539_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_538_, 1);
                    leanh::lean_ctor_set(v___x_538_, 0, v_a_535_);
                    v___x_553_ = v___x_538_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_555_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_535_);
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
                    v_reuseFailAlloc_566_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
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
                    v_reuseFailAlloc_574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
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
    mut v___x_576_: *mut leanh::LeanObject,
    mut v_tk_577_: *mut leanh::LeanObject,
    mut v___x_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
    mut v___y_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
    mut v___y_584_: *mut leanh::LeanObject,
    mut v___y_585_: *mut leanh::LeanObject,
    mut v___y_586_: *mut leanh::LeanObject,
    mut v___y_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2252__boxed_588_: u8 = 0;
    let mut v_res_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2252__boxed_588_ = (leanh::lean_unbox(v___x_578_) as u8);
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
    leanh::lean_dec(v___y_586_);
    leanh::lean_dec_ref(v___y_585_);
    leanh::lean_dec(v___y_584_);
    leanh::lean_dec_ref(v___y_583_);
    leanh::lean_dec(v___y_582_);
    leanh::lean_dec_ref(v___y_581_);
    leanh::lean_dec(v___y_580_);
    leanh::lean_dec_ref(v___y_579_);
    return v_res_589_;
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_evalShowTerm(
    mut v_stx_599_: *mut leanh::LeanObject,
    mut v_a_600_: *mut leanh::LeanObject,
    mut v_a_601_: *mut leanh::LeanObject,
    mut v_a_602_: *mut leanh::LeanObject,
    mut v_a_603_: *mut leanh::LeanObject,
    mut v_a_604_: *mut leanh::LeanObject,
    mut v_a_605_: *mut leanh::LeanObject,
    mut v_a_606_: *mut leanh::LeanObject,
    mut v_a_607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    v___x_609_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4;
    leanh::lean_inc(v_stx_599_);
    v___x_610_ = l_Lean_Syntax_isOfKind(v_stx_599_, v___x_609_);
    if v___x_610_ == 0 {
        let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_599_);
        v___x_611_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg();
        return v___x_611_;
    } else {
        let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tk_613_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_612_ = leanh::lean_unsigned_to_nat(0);
        v_tk_613_ = l_Lean_Syntax_getArg(v_stx_599_, v___x_612_);
        v___x_614_ = leanh::lean_unsigned_to_nat(1);
        v___x_615_ = l_Lean_Syntax_getArg(v_stx_599_, v___x_614_);
        leanh::lean_dec(v_stx_599_);
        v___x_616_ = leanh::lean_box((v___x_610_) as usize);
        v___f_617_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___lam__0___boxed as *mut core::ffi::c_void,
            12,
            3,
        );
        leanh::lean_closure_set(v___f_617_, 0, v___x_615_);
        leanh::lean_closure_set(v___f_617_, 1, v_tk_613_);
        leanh::lean_closure_set(v___f_617_, 2, v___x_616_);
        v___x_618_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_617_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_,
            v_a_607_,
        );
        return v___x_618_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___boxed(
    mut v_stx_619_: *mut leanh::LeanObject,
    mut v_a_620_: *mut leanh::LeanObject,
    mut v_a_621_: *mut leanh::LeanObject,
    mut v_a_622_: *mut leanh::LeanObject,
    mut v_a_623_: *mut leanh::LeanObject,
    mut v_a_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
    mut v_a_626_: *mut leanh::LeanObject,
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm(
        v_stx_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_,
    );
    leanh::lean_dec(v_a_627_);
    leanh::lean_dec_ref(v_a_626_);
    leanh::lean_dec(v_a_625_);
    leanh::lean_dec_ref(v_a_624_);
    leanh::lean_dec(v_a_623_);
    leanh::lean_dec_ref(v_a_622_);
    leanh::lean_dec(v_a_621_);
    leanh::lean_dec_ref(v_a_620_);
    return v_res_629_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1()
-> *mut leanh::LeanObject {
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_641_ = l_Lean_Elab_Tactic_ShowTerm_evalShowTerm___closed__4;
    v___x_642_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3;
    v___x_643_ = leanh::lean_alloc_closure(
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
    mut v_a_645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1();
    return v_res_646_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1___closed__3;
    v___x_674_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___closed__6;
    v___x_675_ = l_Lean_addBuiltinDeclarationRanges(v___x_673_, v___x_674_);
    return v___x_675_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3___boxed(
    mut v_a_676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3();
    return v_res_677_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_evalShowTerm_spec__0___redArg___closed__0);
    v___x_680_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_680_, 0, v___x_679_);
    return v___x_680_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg___boxed(
    mut v___y_681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_682_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
    return v_res_682_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0(
    mut v_00_u03b1_683_: *mut leanh::LeanObject,
    mut v___y_684_: *mut leanh::LeanObject,
    mut v___y_685_: *mut leanh::LeanObject,
    mut v___y_686_: *mut leanh::LeanObject,
    mut v___y_687_: *mut leanh::LeanObject,
    mut v___y_688_: *mut leanh::LeanObject,
    mut v___y_689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
    return v___x_691_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___boxed(
    mut v_00_u03b1_692_: *mut leanh::LeanObject,
    mut v___y_693_: *mut leanh::LeanObject,
    mut v___y_694_: *mut leanh::LeanObject,
    mut v___y_695_: *mut leanh::LeanObject,
    mut v___y_696_: *mut leanh::LeanObject,
    mut v___y_697_: *mut leanh::LeanObject,
    mut v___y_698_: *mut leanh::LeanObject,
    mut v___y_699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_700_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_698_);
    leanh::lean_dec_ref(v___y_697_);
    leanh::lean_dec(v___y_696_);
    leanh::lean_dec_ref(v___y_695_);
    leanh::lean_dec(v___y_694_);
    leanh::lean_dec_ref(v___y_693_);
    return v_res_700_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(
    mut v_e_701_: *mut leanh::LeanObject,
    mut v___y_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_718_: u8 = 0;
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut v_unused_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_704_ = l_Lean_Expr_hasMVar(v_e_701_);
                if v___x_704_ == 0 {
                    v___x_705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_705_, 0, v_e_701_);
                    return v___x_705_;
                } else {
                    v___x_706_ = lean_st_ref_get(v___y_702_);
                    v_mctx_707_ = leanh::lean_ctor_get(v___x_706_, 0);
                    leanh::lean_inc_ref(v_mctx_707_);
                    leanh::lean_dec(v___x_706_);
                    v___x_708_ = l_Lean_instantiateMVarsCore(v_mctx_707_, v_e_701_);
                    v_fst_709_ = leanh::lean_ctor_get(v___x_708_, 0);
                    leanh::lean_inc(v_fst_709_);
                    v_snd_710_ = leanh::lean_ctor_get(v___x_708_, 1);
                    leanh::lean_inc(v_snd_710_);
                    leanh::lean_dec_ref(v___x_708_);
                    v___x_711_ = lean_st_ref_take(v___y_702_);
                    v_cache_712_ = leanh::lean_ctor_get(v___x_711_, 1);
                    v_zetaDeltaFVarIds_713_ = leanh::lean_ctor_get(v___x_711_, 2);
                    v_postponed_714_ = leanh::lean_ctor_get(v___x_711_, 3);
                    v_diag_715_ = leanh::lean_ctor_get(v___x_711_, 4);
                    v_isSharedCheck_724_ = (!leanh::lean_is_exclusive(v___x_711_)) as u8;
                    if v_isSharedCheck_724_ == 0 {
                        v_unused_725_ = leanh::lean_ctor_get(v___x_711_, 0);
                        leanh::lean_dec(v_unused_725_);
                        v___x_717_ = v___x_711_;
                        v_isShared_718_ = v_isSharedCheck_724_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_715_);
                        leanh::lean_inc(v_postponed_714_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_713_);
                        leanh::lean_inc(v_cache_712_);
                        leanh::lean_dec(v___x_711_);
                        v___x_717_ = leanh::lean_box(0);
                        v_isShared_718_ = v_isSharedCheck_724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_718_ == 0 {
                    leanh::lean_ctor_set(v___x_717_, 0, v_snd_710_);
                    v___x_720_ = v___x_717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_723_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_723_, 0, v_snd_710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_723_, 1, v_cache_712_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_723_, 2, v_zetaDeltaFVarIds_713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_723_, 3, v_postponed_714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_723_, 4, v_diag_715_);
                    v___x_720_ = v_reuseFailAlloc_723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_721_ = lean_st_ref_set(v___y_702_, v___x_720_);
                v___x_722_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_722_, 0, v_fst_709_);
                return v___x_722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg___boxed(
    mut v_e_726_: *mut leanh::LeanObject,
    mut v___y_727_: *mut leanh::LeanObject,
    mut v___y_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(
            v_e_726_, v___y_727_,
        );
    leanh::lean_dec(v___y_727_);
    return v_res_729_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1(
    mut v_e_730_: *mut leanh::LeanObject,
    mut v___y_731_: *mut leanh::LeanObject,
    mut v___y_732_: *mut leanh::LeanObject,
    mut v___y_733_: *mut leanh::LeanObject,
    mut v___y_734_: *mut leanh::LeanObject,
    mut v___y_735_: *mut leanh::LeanObject,
    mut v___y_736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(
            v_e_730_, v___y_734_,
        );
    return v___x_738_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___boxed(
    mut v_e_739_: *mut leanh::LeanObject,
    mut v___y_740_: *mut leanh::LeanObject,
    mut v___y_741_: *mut leanh::LeanObject,
    mut v___y_742_: *mut leanh::LeanObject,
    mut v___y_743_: *mut leanh::LeanObject,
    mut v___y_744_: *mut leanh::LeanObject,
    mut v___y_745_: *mut leanh::LeanObject,
    mut v___y_746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_747_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1(
        v_e_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_,
    );
    leanh::lean_dec(v___y_745_);
    leanh::lean_dec_ref(v___y_744_);
    leanh::lean_dec(v___y_743_);
    leanh::lean_dec_ref(v___y_742_);
    leanh::lean_dec(v___y_741_);
    leanh::lean_dec_ref(v___y_740_);
    return v_res_747_;
}
pub unsafe fn l_Lean_Elab_Tactic_ShowTerm_elabShowTerm(
    mut v_x_756_: *mut leanh::LeanObject,
    mut v_x_757_: *mut leanh::LeanObject,
    mut v_a_758_: *mut leanh::LeanObject,
    mut v_a_759_: *mut leanh::LeanObject,
    mut v_a_760_: *mut leanh::LeanObject,
    mut v_a_761_: *mut leanh::LeanObject,
    mut v_a_762_: *mut leanh::LeanObject,
    mut v_a_763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: u8 = 0;
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_779_: u8 = 0;
    let mut v_ref_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
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
    let mut v_reuseFailAlloc_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut v_a_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_809_: u8 = 0;
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_765_ = l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2;
                leanh::lean_inc(v_x_756_);
                v___x_766_ = l_Lean_Syntax_isOfKind(v_x_756_, v___x_765_);
                if v___x_766_ == 0 {
                    leanh::lean_dec(v_x_757_);
                    leanh::lean_dec(v_x_756_);
                    v___x_767_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__0___redArg();
                    return v___x_767_;
                } else {
                    v___x_768_ = leanh::lean_unsigned_to_nat(1);
                    v___x_769_ = l_Lean_Syntax_getArg(v_x_756_, v___x_768_);
                    v___x_770_ = leanh::lean_box(0);
                    v___x_771_ = l_Lean_Elab_Term_elabTermEnsuringType(
                        v___x_769_, v_x_757_, v___x_766_, v___x_766_, v___x_770_, v_a_758_,
                        v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_,
                    );
                    if leanh::lean_obj_tag(v___x_771_) == 0 {
                        v_a_772_ = leanh::lean_ctor_get(v___x_771_, 0);
                        leanh::lean_inc(v_a_772_);
                        leanh::lean_dec_ref_known(v___x_771_, 1);
                        v___x_773_ = 0;
                        v___x_774_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                            v___x_773_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_,
                        );
                        if leanh::lean_obj_tag(v___x_774_) == 0 {
                            leanh::lean_dec_ref_known(v___x_774_, 1);
                            leanh::lean_inc(v_a_772_);
                            v___x_775_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_ShowTerm_elabShowTerm_spec__1___redArg(v_a_772_, v_a_761_);
                            v_a_776_ = leanh::lean_ctor_get(v___x_775_, 0);
                            v_isSharedCheck_805_ =
                                (!leanh::lean_is_exclusive(v___x_775_)) as u8;
                            if v_isSharedCheck_805_ == 0 {
                                v___x_778_ = v___x_775_;
                                v_isShared_779_ = v_isSharedCheck_805_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_776_);
                                leanh::lean_dec(v___x_775_);
                                v___x_778_ = leanh::lean_box(0);
                                v_isShared_779_ = v_isSharedCheck_805_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_772_);
                            leanh::lean_dec(v_x_756_);
                            v_a_806_ = leanh::lean_ctor_get(v___x_774_, 0);
                            v_isSharedCheck_813_ =
                                (!leanh::lean_is_exclusive(v___x_774_)) as u8;
                            if v_isSharedCheck_813_ == 0 {
                                v___x_808_ = v___x_774_;
                                v_isShared_809_ = v_isSharedCheck_813_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_806_);
                                leanh::lean_dec(v___x_774_);
                                v___x_808_ = leanh::lean_box(0);
                                v_isShared_809_ = v_isSharedCheck_813_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_x_756_);
                        return v___x_771_;
                    }
                }
            }
            1 => {
                v_ref_780_ = leanh::lean_ctor_get(v_a_762_, 5);
                v___x_781_ = leanh::lean_unsigned_to_nat(0);
                v_tk_782_ = l_Lean_Syntax_getArg(v_x_756_, v___x_781_);
                leanh::lean_dec(v_x_756_);
                v___x_783_ = l_Lean_Expr_headBeta(v_a_776_);
                leanh::lean_inc(v_ref_780_);
                if v_isShared_779_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_778_, 1);
                    leanh::lean_ctor_set(v___x_778_, 0, v_ref_780_);
                    v___x_785_ = v___x_778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_804_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v_ref_780_);
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
                if leanh::lean_obj_tag(v___x_787_) == 0 {
                    v_isSharedCheck_794_ = (!leanh::lean_is_exclusive(v___x_787_)) as u8;
                    if v_isSharedCheck_794_ == 0 {
                        v_unused_795_ = leanh::lean_ctor_get(v___x_787_, 0);
                        leanh::lean_dec(v_unused_795_);
                        v___x_789_ = v___x_787_;
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_787_);
                        v___x_789_ = leanh::lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_772_);
                    v_a_796_ = leanh::lean_ctor_get(v___x_787_, 0);
                    v_isSharedCheck_803_ = (!leanh::lean_is_exclusive(v___x_787_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_798_ = v___x_787_;
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_796_);
                        leanh::lean_dec(v___x_787_);
                        v___x_798_ = leanh::lean_box(0);
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_790_ == 0 {
                    leanh::lean_ctor_set(v___x_789_, 0, v_a_772_);
                    v___x_792_ = v___x_789_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_772_);
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
                    v_reuseFailAlloc_802_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
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
                    v_reuseFailAlloc_812_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
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
    mut v_x_814_: *mut leanh::LeanObject,
    mut v_x_815_: *mut leanh::LeanObject,
    mut v_a_816_: *mut leanh::LeanObject,
    mut v_a_817_: *mut leanh::LeanObject,
    mut v_a_818_: *mut leanh::LeanObject,
    mut v_a_819_: *mut leanh::LeanObject,
    mut v_a_820_: *mut leanh::LeanObject,
    mut v_a_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Lean_Elab_Tactic_ShowTerm_elabShowTerm(
        v_x_814_, v_x_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_,
    );
    leanh::lean_dec(v_a_821_);
    leanh::lean_dec_ref(v_a_820_);
    leanh::lean_dec(v_a_819_);
    leanh::lean_dec_ref(v_a_818_);
    leanh::lean_dec(v_a_817_);
    leanh::lean_dec_ref(v_a_816_);
    return v_res_823_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1()
-> *mut leanh::LeanObject {
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_833_ = l_Lean_Elab_Tactic_ShowTerm_elabShowTerm___closed__2;
    v___x_834_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1;
    v___x_835_ = leanh::lean_alloc_closure(
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
    mut v_a_837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1();
    return v_res_838_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3()
-> *mut leanh::LeanObject {
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_841_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1;
    v___x_842_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___closed__0;
    v___x_843_ = l_Lean_addBuiltinDocString(v___x_841_, v___x_842_);
    return v___x_843_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3___boxed(
    mut v_a_844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3();
    return v_res_845_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5()
-> *mut leanh::LeanObject {
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1___closed__1;
    v___x_873_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___closed__6;
    v___x_874_ = l_Lean_addBuiltinDeclarationRanges(v___x_872_, v___x_873_);
    return v___x_874_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5___boxed(
    mut v_a_875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_876_ = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5();
    return v_res_876_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_ShowTerm(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ElabRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_evalShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_evalShowTerm_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_docString__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_ShowTerm_0__Lean_Elab_Tactic_ShowTerm_elabShowTerm___regBuiltin_Lean_Elab_Tactic_ShowTerm_elabShowTerm_declRange__5();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_ShowTerm(
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
pub unsafe fn initialize_Lean_Elab_Tactic_ShowTerm(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ElabRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ShowTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_ShowTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_ShowTerm(builtin);
}