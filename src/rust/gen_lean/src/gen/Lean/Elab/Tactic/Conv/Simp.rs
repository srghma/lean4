// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Simp
// Imports: Lean.Elab.Tactic.Split Lean.Elab.Tactic.Conv.Basic Lean.Elab.Tactic.SimpTrace
use crate::ffi::lean_mk_empty_array_with_capacity;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Array_mkArray3___redArg, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node6,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_changeLhs,
    l_Lean_Elab_Tactic_Conv_getLhs___redArg, l_Lean_Elab_Tactic_Conv_updateLhs,
    runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Simp::{
    l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg, l_Lean_Elab_Tactic_mkSimpContext,
};
use crate::r#gen::Lean::Elab::Tactic::SimpTrace::{
    initialize_Lean_Elab_Tactic_SimpTrace, l_Lean_Elab_Tactic_mkSimpCallStx,
    runtime_initialize_Lean_Elab_Tactic_SimpTrace,
};
use crate::r#gen::Lean::Elab::Tactic::Split::{
    initialize_Lean_Elab_Tactic_Split, runtime_initialize_Lean_Elab_Tactic_Split,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_MessageData_nil;
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::l_Lean_Meta_getSimpTheorems___boxed;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{l_Lean_Meta_dsimp, l_Lean_Meta_simp};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Result_getProof;
use crate::r#gen::Lean::Meta::Tactic::Split::l_Lean_Meta_Split_simpMatch;
use crate::r#gen::Lean::Meta::Tactic::TryThis::l_Lean_Meta_Tactic_TryThis_addSuggestion;
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalSimp___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_getSimpTheorems___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Conv_evalSimp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimp___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,2622230176999461939 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4_value) as *mut leanh::LeanObject,14621726445050439147 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__7_value) as *mut leanh::LeanObject,13351543798210616694 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 24 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 24 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 59 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 59 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__1_value)
            as *mut leanh::LeanObject,
        16145843736367156323 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3_value:
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
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4_value:
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
    m_data: [91, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5_value:
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
    m_data: [93, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7_value:
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
    m_data: [111, 110, 108, 121, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11_value:
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
    m_data: [115, 105, 109, 112, 65, 114, 103, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,2622230176999461939 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__0_value)
            as *mut leanh::LeanObject,
        4033974689118230740 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__0_value) as *mut leanh::LeanObject,16766288616492194285 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 105, 109, 112, 77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,2622230176999461939 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__0_value) as *mut leanh::LeanObject,2709596213829771159 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__2_value) as *mut leanh::LeanObject,13624115421224297802 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 69 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 69 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,2622230176999461939 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0_value) as *mut leanh::LeanObject,682381425026147175 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 68, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__2_value) as *mut leanh::LeanObject,5014538692942607590 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 61 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 61 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0_value:
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
    m_data: [100, 115, 105, 109, 112, 65, 114, 103, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value:
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
    m_data: [100, 115, 105, 109, 112, 84, 114, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,2622230176999461939 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__0_value)
            as *mut leanh::LeanObject,
        1408925737459485508 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 68, 83, 105, 109, 112, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__6_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__3_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__0_value) as *mut leanh::LeanObject,7214738609362602633 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Conv_applySimpResult(
    mut v_result_1211_: *mut leanh::LeanObject,
    mut v_a_1212_: *mut leanh::LeanObject,
    mut v_a_1213_: *mut leanh::LeanObject,
    mut v_a_1214_: *mut leanh::LeanObject,
    mut v_a_1215_: *mut leanh::LeanObject,
    mut v_a_1216_: *mut leanh::LeanObject,
    mut v_a_1217_: *mut leanh::LeanObject,
    mut v_a_1218_: *mut leanh::LeanObject,
    mut v_a_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_proof_x3f_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_proof_x3f_1221_ = leanh::lean_ctor_get(v_result_1211_, 1);
                if leanh::lean_obj_tag(v_proof_x3f_1221_) == 0 {
                    v_expr_1222_ = leanh::lean_ctor_get(v_result_1211_, 0);
                    leanh::lean_inc_ref(v_expr_1222_);
                    leanh::lean_dec_ref(v_result_1211_);
                    v___x_1223_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                        v_expr_1222_,
                        v_a_1212_,
                        v_a_1213_,
                        v_a_1214_,
                        v_a_1215_,
                        v_a_1216_,
                        v_a_1217_,
                        v_a_1218_,
                        v_a_1219_,
                    );
                    return v___x_1223_;
                } else {
                    v_expr_1224_ = leanh::lean_ctor_get(v_result_1211_, 0);
                    leanh::lean_inc_ref(v_expr_1224_);
                    v___x_1225_ = l_Lean_Meta_Simp_Result_getProof(
                        v_result_1211_,
                        v_a_1216_,
                        v_a_1217_,
                        v_a_1218_,
                        v_a_1219_,
                    );
                    if leanh::lean_obj_tag(v___x_1225_) == 0 {
                        v_a_1226_ = leanh::lean_ctor_get(v___x_1225_, 0);
                        leanh::lean_inc(v_a_1226_);
                        leanh::lean_dec_ref_known(v___x_1225_, 1);
                        v___x_1227_ = l_Lean_Elab_Tactic_Conv_updateLhs(
                            v_expr_1224_,
                            v_a_1226_,
                            v_a_1212_,
                            v_a_1213_,
                            v_a_1214_,
                            v_a_1215_,
                            v_a_1216_,
                            v_a_1217_,
                            v_a_1218_,
                            v_a_1219_,
                        );
                        return v___x_1227_;
                    } else {
                        leanh::lean_dec_ref(v_expr_1224_);
                        v_a_1228_ = leanh::lean_ctor_get(v___x_1225_, 0);
                        v_isSharedCheck_1235_ =
                            (!leanh::lean_is_exclusive(v___x_1225_)) as u8;
                        if v_isSharedCheck_1235_ == 0 {
                            v___x_1230_ = v___x_1225_;
                            v_isShared_1231_ = v_isSharedCheck_1235_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1228_);
                            leanh::lean_dec(v___x_1225_);
                            v___x_1230_ = leanh::lean_box(0);
                            v_isShared_1231_ = v_isSharedCheck_1235_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1231_ == 0 {
                    v___x_1233_ = v___x_1230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1234_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
                    v___x_1233_ = v_reuseFailAlloc_1234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_applySimpResult___boxed(
    mut v_result_1236_: *mut leanh::LeanObject,
    mut v_a_1237_: *mut leanh::LeanObject,
    mut v_a_1238_: *mut leanh::LeanObject,
    mut v_a_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
    mut v_a_1241_: *mut leanh::LeanObject,
    mut v_a_1242_: *mut leanh::LeanObject,
    mut v_a_1243_: *mut leanh::LeanObject,
    mut v_a_1244_: *mut leanh::LeanObject,
    mut v_a_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
        v_result_1236_,
        v_a_1237_,
        v_a_1238_,
        v_a_1239_,
        v_a_1240_,
        v_a_1241_,
        v_a_1242_,
        v_a_1243_,
        v_a_1244_,
    );
    leanh::lean_dec(v_a_1244_);
    leanh::lean_dec_ref(v_a_1243_);
    leanh::lean_dec(v_a_1242_);
    leanh::lean_dec_ref(v_a_1241_);
    leanh::lean_dec(v_a_1240_);
    leanh::lean_dec_ref(v_a_1239_);
    leanh::lean_dec(v_a_1238_);
    leanh::lean_dec_ref(v_a_1237_);
    return v_res_1246_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1247_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1248_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__0,
    );
    v___x_1249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1249_, 0, v___x_1248_);
    return v___x_1249_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1250_ = leanh::lean_unsigned_to_nat(0);
    v___x_1251_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1,
    );
    v___x_1252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1252_, 0, v___x_1251_);
    leanh::lean_ctor_set(v___x_1252_, 1, v___x_1250_);
    return v___x_1252_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1253_ = leanh::lean_unsigned_to_nat(32);
    v___x_1254_ = lean_mk_empty_array_with_capacity(v___x_1253_);
    v___x_1255_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1255_, 0, v___x_1254_);
    return v___x_1255_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1256_: usize = 0;
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1256_ = 5usize;
    v___x_1257_ = leanh::lean_unsigned_to_nat(0);
    v___x_1258_ = leanh::lean_unsigned_to_nat(32);
    v___x_1259_ = lean_mk_empty_array_with_capacity(v___x_1258_);
    v___x_1260_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3,
    );
    v___x_1261_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1261_, 0, v___x_1260_);
    leanh::lean_ctor_set(v___x_1261_, 1, v___x_1259_);
    leanh::lean_ctor_set(v___x_1261_, 2, v___x_1257_);
    leanh::lean_ctor_set(v___x_1261_, 3, v___x_1257_);
    leanh::lean_ctor_set_usize(v___x_1261_, 4, v___x_1256_);
    return v___x_1261_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1262_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__4,
    );
    v___x_1263_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1,
    );
    v___x_1264_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    leanh::lean_ctor_set(v___x_1264_, 1, v___x_1263_);
    leanh::lean_ctor_set(v___x_1264_, 2, v___x_1263_);
    leanh::lean_ctor_set(v___x_1264_, 3, v___x_1262_);
    return v___x_1264_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1265_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__5,
    );
    v___x_1266_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__2,
    );
    v___x_1267_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1267_, 0, v___x_1266_);
    leanh::lean_ctor_set(v___x_1267_, 1, v___x_1265_);
    return v___x_1267_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(
    mut v_a_1268_: *mut leanh::LeanObject,
    mut v_ctx_1269_: *mut leanh::LeanObject,
    mut v_simprocs_1270_: *mut leanh::LeanObject,
    mut v_d_x3f_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1281_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6,
    );
    v___x_1282_ = l_Lean_Meta_simp(
        v_a_1268_,
        v_ctx_1269_,
        v_simprocs_1270_,
        v_d_x3f_1271_,
        v___x_1281_,
        v___y_1276_,
        v___y_1277_,
        v___y_1278_,
        v___y_1279_,
    );
    return v___x_1282_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed(
    mut v_a_1283_: *mut leanh::LeanObject,
    mut v_ctx_1284_: *mut leanh::LeanObject,
    mut v_simprocs_1285_: *mut leanh::LeanObject,
    mut v_d_x3f_1286_: *mut leanh::LeanObject,
    mut v___y_1287_: *mut leanh::LeanObject,
    mut v___y_1288_: *mut leanh::LeanObject,
    mut v___y_1289_: *mut leanh::LeanObject,
    mut v___y_1290_: *mut leanh::LeanObject,
    mut v___y_1291_: *mut leanh::LeanObject,
    mut v___y_1292_: *mut leanh::LeanObject,
    mut v___y_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__0(
        v_a_1283_,
        v_ctx_1284_,
        v_simprocs_1285_,
        v_d_x3f_1286_,
        v___y_1287_,
        v___y_1288_,
        v___y_1289_,
        v___y_1290_,
        v___y_1291_,
        v___y_1292_,
        v___y_1293_,
        v___y_1294_,
    );
    leanh::lean_dec(v___y_1294_);
    leanh::lean_dec_ref(v___y_1293_);
    leanh::lean_dec(v___y_1292_);
    leanh::lean_dec_ref(v___y_1291_);
    leanh::lean_dec(v___y_1290_);
    leanh::lean_dec_ref(v___y_1289_);
    leanh::lean_dec(v___y_1288_);
    leanh::lean_dec_ref(v___y_1287_);
    return v_res_1296_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(
    mut v_stx_1297_: *mut leanh::LeanObject,
    mut v___x_1298_: u8,
    mut v___x_1299_: u8,
    mut v___x_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
    mut v___y_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut v_a_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut v_a_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1341_: u8 = 0;
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1310_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v_stx_1297_,
                    v___x_1298_,
                    v___x_1299_,
                    v___x_1298_,
                    v___x_1300_,
                    v___y_1301_,
                    v___y_1302_,
                    v___y_1303_,
                    v___y_1304_,
                    v___y_1305_,
                    v___y_1306_,
                    v___y_1307_,
                    v___y_1308_,
                );
                if leanh::lean_obj_tag(v___x_1310_) == 0 {
                    v_a_1311_ = leanh::lean_ctor_get(v___x_1310_, 0);
                    leanh::lean_inc(v_a_1311_);
                    leanh::lean_dec_ref_known(v___x_1310_, 1);
                    v_ctx_1312_ = leanh::lean_ctor_get(v_a_1311_, 0);
                    leanh::lean_inc_ref(v_ctx_1312_);
                    v_simprocs_1313_ = leanh::lean_ctor_get(v_a_1311_, 1);
                    leanh::lean_inc_ref(v_simprocs_1313_);
                    v_dischargeWrapper_1314_ = leanh::lean_ctor_get(v_a_1311_, 2);
                    leanh::lean_inc(v_dischargeWrapper_1314_);
                    leanh::lean_dec(v_a_1311_);
                    v___x_1315_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_1302_,
                        v___y_1305_,
                        v___y_1306_,
                        v___y_1307_,
                        v___y_1308_,
                    );
                    if leanh::lean_obj_tag(v___x_1315_) == 0 {
                        v_a_1316_ = leanh::lean_ctor_get(v___x_1315_, 0);
                        leanh::lean_inc(v_a_1316_);
                        leanh::lean_dec_ref_known(v___x_1315_, 1);
                        v___f_1317_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___boxed
                                as *mut core::ffi::c_void,
                            13,
                            3,
                        );
                        leanh::lean_closure_set(v___f_1317_, 0, v_a_1316_);
                        leanh::lean_closure_set(v___f_1317_, 1, v_ctx_1312_);
                        leanh::lean_closure_set(v___f_1317_, 2, v_simprocs_1313_);
                        v___x_1318_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(
                            v_dischargeWrapper_1314_,
                            v___f_1317_,
                            v___y_1301_,
                            v___y_1302_,
                            v___y_1303_,
                            v___y_1304_,
                            v___y_1305_,
                            v___y_1306_,
                            v___y_1307_,
                            v___y_1308_,
                        );
                        leanh::lean_dec(v_dischargeWrapper_1314_);
                        if leanh::lean_obj_tag(v___x_1318_) == 0 {
                            v_a_1319_ = leanh::lean_ctor_get(v___x_1318_, 0);
                            leanh::lean_inc(v_a_1319_);
                            leanh::lean_dec_ref_known(v___x_1318_, 1);
                            v_fst_1320_ = leanh::lean_ctor_get(v_a_1319_, 0);
                            leanh::lean_inc(v_fst_1320_);
                            leanh::lean_dec(v_a_1319_);
                            v___x_1321_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
                                v_fst_1320_,
                                v___y_1301_,
                                v___y_1302_,
                                v___y_1303_,
                                v___y_1304_,
                                v___y_1305_,
                                v___y_1306_,
                                v___y_1307_,
                                v___y_1308_,
                            );
                            return v___x_1321_;
                        } else {
                            v_a_1322_ = leanh::lean_ctor_get(v___x_1318_, 0);
                            v_isSharedCheck_1329_ =
                                (!leanh::lean_is_exclusive(v___x_1318_)) as u8;
                            if v_isSharedCheck_1329_ == 0 {
                                v___x_1324_ = v___x_1318_;
                                v_isShared_1325_ = v_isSharedCheck_1329_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1322_);
                                leanh::lean_dec(v___x_1318_);
                                v___x_1324_ = leanh::lean_box(0);
                                v_isShared_1325_ = v_isSharedCheck_1329_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_dischargeWrapper_1314_);
                        leanh::lean_dec_ref(v_simprocs_1313_);
                        leanh::lean_dec_ref(v_ctx_1312_);
                        v_a_1330_ = leanh::lean_ctor_get(v___x_1315_, 0);
                        v_isSharedCheck_1337_ =
                            (!leanh::lean_is_exclusive(v___x_1315_)) as u8;
                        if v_isSharedCheck_1337_ == 0 {
                            v___x_1332_ = v___x_1315_;
                            v_isShared_1333_ = v_isSharedCheck_1337_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1330_);
                            leanh::lean_dec(v___x_1315_);
                            v___x_1332_ = leanh::lean_box(0);
                            v_isShared_1333_ = v_isSharedCheck_1337_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1338_ = leanh::lean_ctor_get(v___x_1310_, 0);
                    v_isSharedCheck_1345_ = (!leanh::lean_is_exclusive(v___x_1310_)) as u8;
                    if v_isSharedCheck_1345_ == 0 {
                        v___x_1340_ = v___x_1310_;
                        v_isShared_1341_ = v_isSharedCheck_1345_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1338_);
                        leanh::lean_dec(v___x_1310_);
                        v___x_1340_ = leanh::lean_box(0);
                        v_isShared_1341_ = v_isSharedCheck_1345_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1325_ == 0 {
                    v___x_1327_ = v___x_1324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
                    v___x_1327_ = v_reuseFailAlloc_1328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1327_;
            }
            3 => {
                if v_isShared_1333_ == 0 {
                    v___x_1335_ = v___x_1332_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
                    v___x_1335_ = v_reuseFailAlloc_1336_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1335_;
            }
            5 => {
                if v_isShared_1341_ == 0 {
                    v___x_1343_ = v___x_1340_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed(
    mut v_stx_1346_: *mut leanh::LeanObject,
    mut v___x_1347_: *mut leanh::LeanObject,
    mut v___x_1348_: *mut leanh::LeanObject,
    mut v___x_1349_: *mut leanh::LeanObject,
    mut v___y_1350_: *mut leanh::LeanObject,
    mut v___y_1351_: *mut leanh::LeanObject,
    mut v___y_1352_: *mut leanh::LeanObject,
    mut v___y_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
    mut v___y_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
    mut v___y_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_754__boxed_1359_: u8 = 0;
    let mut v___x_755__boxed_1360_: u8 = 0;
    let mut v_res_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_754__boxed_1359_ = (leanh::lean_unbox(v___x_1347_) as u8);
    v___x_755__boxed_1360_ = (leanh::lean_unbox(v___x_1348_) as u8);
    v_res_1361_ = l_Lean_Elab_Tactic_Conv_evalSimp___lam__1(
        v_stx_1346_,
        v___x_754__boxed_1359_,
        v___x_755__boxed_1360_,
        v___x_1349_,
        v___y_1350_,
        v___y_1351_,
        v___y_1352_,
        v___y_1353_,
        v___y_1354_,
        v___y_1355_,
        v___y_1356_,
        v___y_1357_,
    );
    leanh::lean_dec(v___y_1357_);
    leanh::lean_dec_ref(v___y_1356_);
    leanh::lean_dec(v___y_1355_);
    leanh::lean_dec_ref(v___y_1354_);
    leanh::lean_dec(v___y_1353_);
    leanh::lean_dec_ref(v___y_1352_);
    leanh::lean_dec(v___y_1351_);
    leanh::lean_dec_ref(v___y_1350_);
    leanh::lean_dec(v_stx_1346_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp(
    mut v_stx_1363_: *mut leanh::LeanObject,
    mut v_a_1364_: *mut leanh::LeanObject,
    mut v_a_1365_: *mut leanh::LeanObject,
    mut v_a_1366_: *mut leanh::LeanObject,
    mut v_a_1367_: *mut leanh::LeanObject,
    mut v_a_1368_: *mut leanh::LeanObject,
    mut v_a_1369_: *mut leanh::LeanObject,
    mut v_a_1370_: *mut leanh::LeanObject,
    mut v_a_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1373_: u8 = 0;
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1373_ = 0;
    v___x_1374_ = 0;
    v___x_1375_ = l_Lean_Elab_Tactic_Conv_evalSimp___closed__0;
    v___x_1376_ = leanh::lean_box((v___x_1373_) as usize);
    v___x_1377_ = leanh::lean_box((v___x_1374_) as usize);
    v___f_1378_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimp___lam__1___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    leanh::lean_closure_set(v___f_1378_, 0, v_stx_1363_);
    leanh::lean_closure_set(v___f_1378_, 1, v___x_1376_);
    leanh::lean_closure_set(v___f_1378_, 2, v___x_1377_);
    leanh::lean_closure_set(v___f_1378_, 3, v___x_1375_);
    v___x_1379_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_1378_,
        v_a_1364_,
        v_a_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
        v_a_1370_,
        v_a_1371_,
    );
    return v___x_1379_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimp___boxed(
    mut v_stx_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_a_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
    mut v_a_1385_: *mut leanh::LeanObject,
    mut v_a_1386_: *mut leanh::LeanObject,
    mut v_a_1387_: *mut leanh::LeanObject,
    mut v_a_1388_: *mut leanh::LeanObject,
    mut v_a_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_Lean_Elab_Tactic_Conv_evalSimp(
        v_stx_1380_,
        v_a_1381_,
        v_a_1382_,
        v_a_1383_,
        v_a_1384_,
        v_a_1385_,
        v_a_1386_,
        v_a_1387_,
        v_a_1388_,
    );
    leanh::lean_dec(v_a_1388_);
    leanh::lean_dec_ref(v_a_1387_);
    leanh::lean_dec(v_a_1386_);
    leanh::lean_dec_ref(v_a_1385_);
    leanh::lean_dec(v_a_1384_);
    leanh::lean_dec_ref(v_a_1383_);
    leanh::lean_dec(v_a_1382_);
    leanh::lean_dec_ref(v_a_1381_);
    return v_res_1390_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1()
-> *mut leanh::LeanObject {
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1412_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__5;
    v___x_1413_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8;
    v___x_1414_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimp___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1415_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1411_,
        v___x_1412_,
        v___x_1413_,
        v___x_1414_,
    );
    return v___x_1415_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___boxed(
    mut v_a_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
    return v_res_1417_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__8;
    v___x_1444_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___closed__6;
    v___x_1445_ = l_Lean_addBuiltinDeclarationRanges(v___x_1443_, v___x_1444_);
    return v___x_1445_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3___boxed(
    mut v_a_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1447_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
    return v_res_1447_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1448_ = leanh::lean_box(0);
    v___x_1449_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1450_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1450_, 0, v___x_1449_);
    leanh::lean_ctor_set(v___x_1450_, 1, v___x_1448_);
    return v___x_1450_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___closed__0);
    v___x_1453_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1453_, 0, v___x_1452_);
    return v___x_1453_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg___boxed(
    mut v___y_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
    return v_res_1455_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(
    mut v_00_u03b1_1456_: *mut leanh::LeanObject,
    mut v___y_1457_: *mut leanh::LeanObject,
    mut v___y_1458_: *mut leanh::LeanObject,
    mut v___y_1459_: *mut leanh::LeanObject,
    mut v___y_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
    mut v___y_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1466_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
    return v___x_1466_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___boxed(
    mut v_00_u03b1_1467_: *mut leanh::LeanObject,
    mut v___y_1468_: *mut leanh::LeanObject,
    mut v___y_1469_: *mut leanh::LeanObject,
    mut v___y_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
    mut v___y_1474_: *mut leanh::LeanObject,
    mut v___y_1475_: *mut leanh::LeanObject,
    mut v___y_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1477_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0(
            v_00_u03b1_1467_,
            v___y_1468_,
            v___y_1469_,
            v___y_1470_,
            v___y_1471_,
            v___y_1472_,
            v___y_1473_,
            v___y_1474_,
            v___y_1475_,
        );
    leanh::lean_dec(v___y_1475_);
    leanh::lean_dec_ref(v___y_1474_);
    leanh::lean_dec(v___y_1473_);
    leanh::lean_dec_ref(v___y_1472_);
    leanh::lean_dec(v___y_1471_);
    leanh::lean_dec_ref(v___y_1470_);
    leanh::lean_dec(v___y_1469_);
    leanh::lean_dec_ref(v___y_1468_);
    return v_res_1477_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(
    mut v___x_1478_: *mut leanh::LeanObject,
    mut v_a_1479_: *mut leanh::LeanObject,
    mut v_ctx_1480_: *mut leanh::LeanObject,
    mut v_simprocs_1481_: *mut leanh::LeanObject,
    mut v_d_x3f_1482_: *mut leanh::LeanObject,
    mut v___y_1483_: *mut leanh::LeanObject,
    mut v___y_1484_: *mut leanh::LeanObject,
    mut v___y_1485_: *mut leanh::LeanObject,
    mut v___y_1486_: *mut leanh::LeanObject,
    mut v___y_1487_: *mut leanh::LeanObject,
    mut v___y_1488_: *mut leanh::LeanObject,
    mut v___y_1489_: *mut leanh::LeanObject,
    mut v___y_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: usize = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__1,
    );
    leanh::lean_inc_n(v___x_1478_, 2);
    v___x_1493_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1493_, 0, v___x_1492_);
    leanh::lean_ctor_set(v___x_1493_, 1, v___x_1478_);
    v___x_1494_ = leanh::lean_unsigned_to_nat(32);
    v___x_1495_ = lean_mk_empty_array_with_capacity(v___x_1494_);
    v___x_1496_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3_once),
        _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__3,
    );
    v___x_1497_ = 5usize;
    v___x_1498_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1498_, 0, v___x_1496_);
    leanh::lean_ctor_set(v___x_1498_, 1, v___x_1495_);
    leanh::lean_ctor_set(v___x_1498_, 2, v___x_1478_);
    leanh::lean_ctor_set(v___x_1498_, 3, v___x_1478_);
    leanh::lean_ctor_set_usize(v___x_1498_, 4, v___x_1497_);
    v___x_1499_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1499_, 0, v___x_1492_);
    leanh::lean_ctor_set(v___x_1499_, 1, v___x_1492_);
    leanh::lean_ctor_set(v___x_1499_, 2, v___x_1492_);
    leanh::lean_ctor_set(v___x_1499_, 3, v___x_1498_);
    v___x_1500_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1500_, 0, v___x_1493_);
    leanh::lean_ctor_set(v___x_1500_, 1, v___x_1499_);
    v___x_1501_ = l_Lean_Meta_simp(
        v_a_1479_,
        v_ctx_1480_,
        v_simprocs_1481_,
        v_d_x3f_1482_,
        v___x_1500_,
        v___y_1487_,
        v___y_1488_,
        v___y_1489_,
        v___y_1490_,
    );
    leanh::lean_dec_ref_known(v___x_1500_, 2);
    return v___x_1501_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed(
    mut v___x_1502_: *mut leanh::LeanObject,
    mut v_a_1503_: *mut leanh::LeanObject,
    mut v_ctx_1504_: *mut leanh::LeanObject,
    mut v_simprocs_1505_: *mut leanh::LeanObject,
    mut v_d_x3f_1506_: *mut leanh::LeanObject,
    mut v___y_1507_: *mut leanh::LeanObject,
    mut v___y_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
    mut v___y_1510_: *mut leanh::LeanObject,
    mut v___y_1511_: *mut leanh::LeanObject,
    mut v___y_1512_: *mut leanh::LeanObject,
    mut v___y_1513_: *mut leanh::LeanObject,
    mut v___y_1514_: *mut leanh::LeanObject,
    mut v___y_1515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1516_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0(
        v___x_1502_,
        v_a_1503_,
        v_ctx_1504_,
        v_simprocs_1505_,
        v_d_x3f_1506_,
        v___y_1507_,
        v___y_1508_,
        v___y_1509_,
        v___y_1510_,
        v___y_1511_,
        v___y_1512_,
        v___y_1513_,
        v___y_1514_,
    );
    leanh::lean_dec(v___y_1514_);
    leanh::lean_dec_ref(v___y_1513_);
    leanh::lean_dec(v___y_1512_);
    leanh::lean_dec_ref(v___y_1511_);
    leanh::lean_dec(v___y_1510_);
    leanh::lean_dec_ref(v___y_1509_);
    leanh::lean_dec(v___y_1508_);
    leanh::lean_dec_ref(v___y_1507_);
    return v_res_1516_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1530_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(
    mut v___x_1532_: u8,
    mut v_stx_1533_: *mut leanh::LeanObject,
    mut v___x_1534_: *mut leanh::LeanObject,
    mut v___x_1535_: *mut leanh::LeanObject,
    mut v___x_1536_: *mut leanh::LeanObject,
    mut v___x_1537_: u8,
    mut v___y_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
    mut v___y_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
    mut v___y_1542_: *mut leanh::LeanObject,
    mut v___y_1543_: *mut leanh::LeanObject,
    mut v___y_1544_: *mut leanh::LeanObject,
    mut v___y_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1565_: u8 = 0;
    let mut v___y_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v_usedTheorems_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1619_: u8 = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_unused_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_unused_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_a_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut v_a_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v___y_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1660_: u8 = 0;
    let mut v___y_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1690_: u8 = 0;
    let mut v___y_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut v_o_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_o_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_1532_ == 0 {
                    leanh::lean_dec_ref(v___x_1536_);
                    leanh::lean_dec_ref(v___x_1535_);
                    leanh::lean_dec_ref(v___x_1534_);
                    v___x_1547_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                    return v___x_1547_;
                } else {
                    v___x_1548_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1549_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1548_);
                    v___x_1550_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0;
                    leanh::lean_inc_ref(v___x_1536_);
                    leanh::lean_inc_ref(v___x_1535_);
                    leanh::lean_inc_ref(v___x_1534_);
                    v___x_1551_ =
                        l_Lean_Name_mkStr4(v___x_1534_, v___x_1535_, v___x_1536_, v___x_1550_);
                    leanh::lean_inc(v___x_1549_);
                    v___x_1552_ = l_Lean_Syntax_isOfKind(v___x_1549_, v___x_1551_);
                    leanh::lean_dec(v___x_1551_);
                    if v___x_1552_ == 0 {
                        leanh::lean_dec(v___x_1549_);
                        leanh::lean_dec_ref(v___x_1536_);
                        leanh::lean_dec_ref(v___x_1535_);
                        leanh::lean_dec_ref(v___x_1534_);
                        v___x_1553_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                        return v___x_1553_;
                    } else {
                        v___x_1554_ = leanh::lean_unsigned_to_nat(0);
                        v_tk_1555_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1554_);
                        v___x_1733_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1734_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1733_);
                        v___x_1780_ = leanh::lean_unsigned_to_nat(3);
                        v___x_1781_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1780_);
                        v___x_1782_ = l_Lean_Syntax_isNone(v___x_1781_);
                        if v___x_1782_ == 0 {
                            leanh::lean_inc(v___x_1781_);
                            v___x_1783_ = l_Lean_Syntax_matchesNull(v___x_1781_, v___x_1548_);
                            if v___x_1783_ == 0 {
                                leanh::lean_dec(v___x_1781_);
                                leanh::lean_dec(v___x_1734_);
                                leanh::lean_dec(v_tk_1555_);
                                leanh::lean_dec(v___x_1549_);
                                leanh::lean_dec_ref(v___x_1536_);
                                leanh::lean_dec_ref(v___x_1535_);
                                leanh::lean_dec_ref(v___x_1534_);
                                v___x_1784_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                                return v___x_1784_;
                            } else {
                                v_o_1785_ = l_Lean_Syntax_getArg(v___x_1781_, v___x_1554_);
                                leanh::lean_dec(v___x_1781_);
                                v___x_1786_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1786_, 0, v_o_1785_);
                                v_o_1757_ = v___x_1786_;
                                v___y_1758_ = v___y_1538_;
                                v___y_1759_ = v___y_1539_;
                                v___y_1760_ = v___y_1540_;
                                v___y_1761_ = v___y_1541_;
                                v___y_1762_ = v___y_1542_;
                                v___y_1763_ = v___y_1543_;
                                v___y_1764_ = v___y_1544_;
                                v___y_1765_ = v___y_1545_;
                                state = 20;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_1781_);
                            v___x_1787_ = leanh::lean_box(0);
                            v_o_1757_ = v___x_1787_;
                            v___y_1758_ = v___y_1538_;
                            v___y_1759_ = v___y_1539_;
                            v___y_1760_ = v___y_1540_;
                            v___y_1761_ = v___y_1541_;
                            v___y_1762_ = v___y_1542_;
                            v___y_1763_ = v___y_1543_;
                            v___y_1764_ = v___y_1544_;
                            v___y_1765_ = v___y_1545_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_1557_, 2);
                v___x_1575_ = l_Array_append___redArg(v___y_1557_, v___y_1574_);
                leanh::lean_dec_ref(v___y_1574_);
                leanh::lean_inc_n(v___y_1564_, 2);
                leanh::lean_inc_n(v___y_1563_, 2);
                v___x_1576_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1576_, 0, v___y_1563_);
                leanh::lean_ctor_set(v___x_1576_, 1, v___y_1564_);
                leanh::lean_ctor_set(v___x_1576_, 2, v___x_1575_);
                v___x_1577_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1577_, 0, v___y_1563_);
                leanh::lean_ctor_set(v___x_1577_, 1, v___y_1564_);
                leanh::lean_ctor_set(v___x_1577_, 2, v___y_1557_);
                v___x_1578_ = l_Lean_Syntax_node6(
                    v___y_1563_,
                    v___y_1561_,
                    v___y_1570_,
                    v___x_1549_,
                    v___y_1569_,
                    v___y_1560_,
                    v___x_1576_,
                    v___x_1577_,
                );
                v___x_1579_ = 0;
                v___x_1580_ = l_Lean_Elab_Tactic_Conv_evalSimp___closed__0;
                v___x_1581_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v___x_1578_,
                    v___y_1565_,
                    v___x_1579_,
                    v___y_1565_,
                    v___x_1580_,
                    v___y_1558_,
                    v___y_1567_,
                    v___y_1566_,
                    v___y_1562_,
                    v___y_1573_,
                    v___y_1568_,
                    v___y_1571_,
                    v___y_1559_,
                );
                if leanh::lean_obj_tag(v___x_1581_) == 0 {
                    v_a_1582_ = leanh::lean_ctor_get(v___x_1581_, 0);
                    leanh::lean_inc(v_a_1582_);
                    leanh::lean_dec_ref_known(v___x_1581_, 1);
                    v_ctx_1583_ = leanh::lean_ctor_get(v_a_1582_, 0);
                    leanh::lean_inc_ref(v_ctx_1583_);
                    v_simprocs_1584_ = leanh::lean_ctor_get(v_a_1582_, 1);
                    leanh::lean_inc_ref(v_simprocs_1584_);
                    v_dischargeWrapper_1585_ = leanh::lean_ctor_get(v_a_1582_, 2);
                    leanh::lean_inc(v_dischargeWrapper_1585_);
                    leanh::lean_dec(v_a_1582_);
                    v___x_1586_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_1567_,
                        v___y_1573_,
                        v___y_1568_,
                        v___y_1571_,
                        v___y_1559_,
                    );
                    if leanh::lean_obj_tag(v___x_1586_) == 0 {
                        v_a_1587_ = leanh::lean_ctor_get(v___x_1586_, 0);
                        leanh::lean_inc(v_a_1587_);
                        leanh::lean_dec_ref_known(v___x_1586_, 1);
                        v___f_1588_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__0___boxed
                                as *mut core::ffi::c_void,
                            14,
                            4,
                        );
                        leanh::lean_closure_set(v___f_1588_, 0, v___x_1554_);
                        leanh::lean_closure_set(v___f_1588_, 1, v_a_1587_);
                        leanh::lean_closure_set(v___f_1588_, 2, v_ctx_1583_);
                        leanh::lean_closure_set(v___f_1588_, 3, v_simprocs_1584_);
                        v___x_1589_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(
                            v_dischargeWrapper_1585_,
                            v___f_1588_,
                            v___y_1558_,
                            v___y_1567_,
                            v___y_1566_,
                            v___y_1562_,
                            v___y_1573_,
                            v___y_1568_,
                            v___y_1571_,
                            v___y_1559_,
                        );
                        leanh::lean_dec(v_dischargeWrapper_1585_);
                        if leanh::lean_obj_tag(v___x_1589_) == 0 {
                            v_a_1590_ = leanh::lean_ctor_get(v___x_1589_, 0);
                            leanh::lean_inc(v_a_1590_);
                            leanh::lean_dec_ref_known(v___x_1589_, 1);
                            v_fst_1591_ = leanh::lean_ctor_get(v_a_1590_, 0);
                            leanh::lean_inc(v_fst_1591_);
                            v_snd_1592_ = leanh::lean_ctor_get(v_a_1590_, 1);
                            leanh::lean_inc(v_snd_1592_);
                            leanh::lean_dec(v_a_1590_);
                            v___x_1593_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
                                v_fst_1591_,
                                v___y_1558_,
                                v___y_1567_,
                                v___y_1566_,
                                v___y_1562_,
                                v___y_1573_,
                                v___y_1568_,
                                v___y_1571_,
                                v___y_1559_,
                            );
                            if leanh::lean_obj_tag(v___x_1593_) == 0 {
                                v_isSharedCheck_1626_ =
                                    (!leanh::lean_is_exclusive(v___x_1593_)) as u8;
                                if v_isSharedCheck_1626_ == 0 {
                                    v_unused_1627_ = leanh::lean_ctor_get(v___x_1593_, 0);
                                    leanh::lean_dec(v_unused_1627_);
                                    v___x_1595_ = v___x_1593_;
                                    v_isShared_1596_ = v_isSharedCheck_1626_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1593_);
                                    v___x_1595_ = leanh::lean_box(0);
                                    v_isShared_1596_ = v_isSharedCheck_1626_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_snd_1592_);
                                leanh::lean_dec(v___x_1578_);
                                leanh::lean_dec(v_tk_1555_);
                                return v___x_1593_;
                            }
                        } else {
                            leanh::lean_dec(v___x_1578_);
                            leanh::lean_dec(v_tk_1555_);
                            v_a_1628_ = leanh::lean_ctor_get(v___x_1589_, 0);
                            v_isSharedCheck_1635_ =
                                (!leanh::lean_is_exclusive(v___x_1589_)) as u8;
                            if v_isSharedCheck_1635_ == 0 {
                                v___x_1630_ = v___x_1589_;
                                v_isShared_1631_ = v_isSharedCheck_1635_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1628_);
                                leanh::lean_dec(v___x_1589_);
                                v___x_1630_ = leanh::lean_box(0);
                                v_isShared_1631_ = v_isSharedCheck_1635_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_dischargeWrapper_1585_);
                        leanh::lean_dec_ref(v_simprocs_1584_);
                        leanh::lean_dec_ref(v_ctx_1583_);
                        leanh::lean_dec(v___x_1578_);
                        leanh::lean_dec(v_tk_1555_);
                        v_a_1636_ = leanh::lean_ctor_get(v___x_1586_, 0);
                        v_isSharedCheck_1643_ =
                            (!leanh::lean_is_exclusive(v___x_1586_)) as u8;
                        if v_isSharedCheck_1643_ == 0 {
                            v___x_1638_ = v___x_1586_;
                            v_isShared_1639_ = v_isSharedCheck_1643_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1636_);
                            leanh::lean_dec(v___x_1586_);
                            v___x_1638_ = leanh::lean_box(0);
                            v_isShared_1639_ = v_isSharedCheck_1643_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1578_);
                    leanh::lean_dec(v_tk_1555_);
                    v_a_1644_ = leanh::lean_ctor_get(v___x_1581_, 0);
                    v_isSharedCheck_1651_ = (!leanh::lean_is_exclusive(v___x_1581_)) as u8;
                    if v_isSharedCheck_1651_ == 0 {
                        v___x_1646_ = v___x_1581_;
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1644_);
                        leanh::lean_dec(v___x_1581_);
                        v___x_1646_ = leanh::lean_box(0);
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_usedTheorems_1597_ = leanh::lean_ctor_get(v_snd_1592_, 0);
                v_isSharedCheck_1624_ = (!leanh::lean_is_exclusive(v_snd_1592_)) as u8;
                if v_isSharedCheck_1624_ == 0 {
                    v_unused_1625_ = leanh::lean_ctor_get(v_snd_1592_, 1);
                    leanh::lean_dec(v_unused_1625_);
                    v___x_1599_ = v_snd_1592_;
                    v_isShared_1600_ = v_isSharedCheck_1624_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_usedTheorems_1597_);
                    leanh::lean_dec(v_snd_1592_);
                    v___x_1599_ = leanh::lean_box(0);
                    v_isShared_1600_ = v_isSharedCheck_1624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1601_ = l_Lean_Elab_Tactic_mkSimpCallStx(
                    v___x_1578_,
                    v_usedTheorems_1597_,
                    v___y_1573_,
                    v___y_1568_,
                    v___y_1571_,
                    v___y_1559_,
                );
                leanh::lean_dec_ref(v_usedTheorems_1597_);
                if leanh::lean_obj_tag(v___x_1601_) == 0 {
                    v_a_1602_ = leanh::lean_ctor_get(v___x_1601_, 0);
                    leanh::lean_inc(v_a_1602_);
                    leanh::lean_dec_ref_known(v___x_1601_, 1);
                    v___x_1603_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2;
                    if v_isShared_1600_ == 0 {
                        leanh::lean_ctor_set(v___x_1599_, 1, v_a_1602_);
                        leanh::lean_ctor_set(v___x_1599_, 0, v___x_1603_);
                        v___x_1605_ = v___x_1599_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1615_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1603_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_a_1602_);
                        v___x_1605_ = v_reuseFailAlloc_1615_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1599_);
                    leanh::lean_del_object(v___x_1595_);
                    leanh::lean_dec(v_tk_1555_);
                    v_a_1616_ = leanh::lean_ctor_get(v___x_1601_, 0);
                    v_isSharedCheck_1623_ = (!leanh::lean_is_exclusive(v___x_1601_)) as u8;
                    if v_isSharedCheck_1623_ == 0 {
                        v___x_1618_ = v___x_1601_;
                        v_isShared_1619_ = v_isSharedCheck_1623_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1616_);
                        leanh::lean_dec(v___x_1601_);
                        v___x_1618_ = leanh::lean_box(0);
                        v_isShared_1619_ = v_isSharedCheck_1623_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1606_ = leanh::lean_box(0);
                v___x_1607_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_1607_, 0, v___x_1605_);
                leanh::lean_ctor_set(v___x_1607_, 1, v___x_1606_);
                leanh::lean_ctor_set(v___x_1607_, 2, v___x_1606_);
                leanh::lean_ctor_set(v___x_1607_, 3, v___x_1606_);
                leanh::lean_ctor_set(v___x_1607_, 4, v___x_1606_);
                leanh::lean_ctor_set(v___x_1607_, 5, v___x_1606_);
                leanh::lean_inc(v___y_1572_);
                if v_isShared_1596_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1595_, 1);
                    leanh::lean_ctor_set(v___x_1595_, 0, v___y_1572_);
                    v___x_1609_ = v___x_1595_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1614_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___y_1572_);
                    v___x_1609_ = v_reuseFailAlloc_1614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1610_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3;
                v___x_1611_ = 4;
                v___x_1612_ = l_Lean_MessageData_nil;
                v___x_1613_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_1555_,
                    v___x_1607_,
                    v___x_1609_,
                    v___x_1610_,
                    v___x_1606_,
                    v___x_1611_,
                    v___x_1612_,
                    v___y_1571_,
                    v___y_1559_,
                );
                return v___x_1613_;
            }
            6 => {
                if v_isShared_1619_ == 0 {
                    v___x_1621_ = v___x_1618_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
                    v___x_1621_ = v_reuseFailAlloc_1622_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1621_;
            }
            8 => {
                if v_isShared_1631_ == 0 {
                    v___x_1633_ = v___x_1630_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1633_;
            }
            10 => {
                if v_isShared_1639_ == 0 {
                    v___x_1641_ = v___x_1638_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1641_;
            }
            12 => {
                if v_isShared_1647_ == 0 {
                    v___x_1649_ = v___x_1646_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
                    v___x_1649_ = v_reuseFailAlloc_1650_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1649_;
            }
            14 => {
                leanh::lean_inc_ref(v___y_1653_);
                v___x_1671_ = l_Array_append___redArg(v___y_1653_, v___y_1670_);
                leanh::lean_dec_ref(v___y_1670_);
                leanh::lean_inc(v___y_1659_);
                leanh::lean_inc(v___y_1658_);
                v___x_1672_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1672_, 0, v___y_1658_);
                leanh::lean_ctor_set(v___x_1672_, 1, v___y_1659_);
                leanh::lean_ctor_set(v___x_1672_, 2, v___x_1671_);
                if leanh::lean_obj_tag(v___y_1662_) == 1 {
                    v_val_1673_ = leanh::lean_ctor_get(v___y_1662_, 0);
                    leanh::lean_inc(v_val_1673_);
                    leanh::lean_dec_ref_known(v___y_1662_, 1);
                    v___x_1674_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4;
                    leanh::lean_inc_n(v___y_1658_, 3);
                    v___x_1675_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1675_, 0, v___y_1658_);
                    leanh::lean_ctor_set(v___x_1675_, 1, v___x_1674_);
                    leanh::lean_inc_ref(v___y_1653_);
                    v___x_1676_ = l_Array_append___redArg(v___y_1653_, v_val_1673_);
                    leanh::lean_dec(v_val_1673_);
                    leanh::lean_inc(v___y_1659_);
                    v___x_1677_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1677_, 0, v___y_1658_);
                    leanh::lean_ctor_set(v___x_1677_, 1, v___y_1659_);
                    leanh::lean_ctor_set(v___x_1677_, 2, v___x_1676_);
                    v___x_1678_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5;
                    v___x_1679_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1679_, 0, v___y_1658_);
                    leanh::lean_ctor_set(v___x_1679_, 1, v___x_1678_);
                    v___x_1680_ = l_Array_mkArray3___redArg(v___x_1675_, v___x_1677_, v___x_1679_);
                    v___y_1557_ = v___y_1653_;
                    v___y_1558_ = v___y_1654_;
                    v___y_1559_ = v___y_1655_;
                    v___y_1560_ = v___x_1672_;
                    v___y_1561_ = v___y_1656_;
                    v___y_1562_ = v___y_1657_;
                    v___y_1563_ = v___y_1658_;
                    v___y_1564_ = v___y_1659_;
                    v___y_1565_ = v___y_1660_;
                    v___y_1566_ = v___y_1661_;
                    v___y_1567_ = v___y_1663_;
                    v___y_1568_ = v___y_1664_;
                    v___y_1569_ = v___y_1665_;
                    v___y_1570_ = v___y_1666_;
                    v___y_1571_ = v___y_1667_;
                    v___y_1572_ = v___y_1669_;
                    v___y_1573_ = v___y_1668_;
                    v___y_1574_ = v___x_1680_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1662_);
                    v___x_1681_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_1557_ = v___y_1653_;
                    v___y_1558_ = v___y_1654_;
                    v___y_1559_ = v___y_1655_;
                    v___y_1560_ = v___x_1672_;
                    v___y_1561_ = v___y_1656_;
                    v___y_1562_ = v___y_1657_;
                    v___y_1563_ = v___y_1658_;
                    v___y_1564_ = v___y_1659_;
                    v___y_1565_ = v___y_1660_;
                    v___y_1566_ = v___y_1661_;
                    v___y_1567_ = v___y_1663_;
                    v___y_1568_ = v___y_1664_;
                    v___y_1569_ = v___y_1665_;
                    v___y_1570_ = v___y_1666_;
                    v___y_1571_ = v___y_1667_;
                    v___y_1572_ = v___y_1669_;
                    v___y_1573_ = v___y_1668_;
                    v___y_1574_ = v___x_1681_;
                    state = 1;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc_ref(v___y_1683_);
                v___x_1701_ = l_Array_append___redArg(v___y_1683_, v___y_1700_);
                leanh::lean_dec_ref(v___y_1700_);
                leanh::lean_inc(v___y_1689_);
                leanh::lean_inc(v___y_1688_);
                v___x_1702_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1702_, 0, v___y_1688_);
                leanh::lean_ctor_set(v___x_1702_, 1, v___y_1689_);
                leanh::lean_ctor_set(v___x_1702_, 2, v___x_1701_);
                if leanh::lean_obj_tag(v___y_1694_) == 1 {
                    v_val_1703_ = leanh::lean_ctor_get(v___y_1694_, 0);
                    leanh::lean_inc(v_val_1703_);
                    leanh::lean_dec_ref_known(v___y_1694_, 1);
                    v___x_1704_ = l_Lean_SourceInfo_fromRef(v_val_1703_, v___x_1537_);
                    leanh::lean_dec(v_val_1703_);
                    v___x_1705_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7;
                    v___x_1706_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1706_, 0, v___x_1704_);
                    leanh::lean_ctor_set(v___x_1706_, 1, v___x_1705_);
                    v___x_1707_ = l_Array_mkArray1___redArg(v___x_1706_);
                    v___y_1653_ = v___y_1683_;
                    v___y_1654_ = v___y_1684_;
                    v___y_1655_ = v___y_1685_;
                    v___y_1656_ = v___y_1686_;
                    v___y_1657_ = v___y_1687_;
                    v___y_1658_ = v___y_1688_;
                    v___y_1659_ = v___y_1689_;
                    v___y_1660_ = v___y_1690_;
                    v___y_1661_ = v___y_1691_;
                    v___y_1662_ = v___y_1692_;
                    v___y_1663_ = v___y_1693_;
                    v___y_1664_ = v___y_1695_;
                    v___y_1665_ = v___x_1702_;
                    v___y_1666_ = v___y_1696_;
                    v___y_1667_ = v___y_1697_;
                    v___y_1668_ = v___y_1699_;
                    v___y_1669_ = v___y_1698_;
                    v___y_1670_ = v___x_1707_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1694_);
                    v___x_1708_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_1653_ = v___y_1683_;
                    v___y_1654_ = v___y_1684_;
                    v___y_1655_ = v___y_1685_;
                    v___y_1656_ = v___y_1686_;
                    v___y_1657_ = v___y_1687_;
                    v___y_1658_ = v___y_1688_;
                    v___y_1659_ = v___y_1689_;
                    v___y_1660_ = v___y_1690_;
                    v___y_1661_ = v___y_1691_;
                    v___y_1662_ = v___y_1692_;
                    v___y_1663_ = v___y_1693_;
                    v___y_1664_ = v___y_1695_;
                    v___y_1665_ = v___x_1702_;
                    v___y_1666_ = v___y_1696_;
                    v___y_1667_ = v___y_1697_;
                    v___y_1668_ = v___y_1699_;
                    v___y_1669_ = v___y_1698_;
                    v___y_1670_ = v___x_1708_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v_ref_1721_ = leanh::lean_ctor_get(v___y_1718_, 5);
                v___x_1722_ = 0;
                v___x_1723_ = l_Lean_SourceInfo_fromRef(v_ref_1721_, v___x_1722_);
                v___x_1724_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__4;
                v___x_1725_ =
                    l_Lean_Name_mkStr4(v___x_1534_, v___x_1535_, v___x_1536_, v___x_1724_);
                v___x_1726_ = l_Lean_SourceInfo_fromRef(v_tk_1555_, v___x_1537_);
                v___x_1727_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1727_, 0, v___x_1726_);
                leanh::lean_ctor_set(v___x_1727_, 1, v___x_1724_);
                v___x_1728_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9;
                v___x_1729_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10,
                );
                if leanh::lean_obj_tag(v___y_1720_) == 1 {
                    v_val_1730_ = leanh::lean_ctor_get(v___y_1720_, 0);
                    leanh::lean_inc(v_val_1730_);
                    leanh::lean_dec_ref_known(v___y_1720_, 1);
                    v___x_1731_ = l_Array_mkArray1___redArg(v_val_1730_);
                    v___y_1683_ = v___x_1729_;
                    v___y_1684_ = v___y_1712_;
                    v___y_1685_ = v___y_1714_;
                    v___y_1686_ = v___x_1725_;
                    v___y_1687_ = v___y_1717_;
                    v___y_1688_ = v___x_1723_;
                    v___y_1689_ = v___x_1728_;
                    v___y_1690_ = v___x_1722_;
                    v___y_1691_ = v___y_1710_;
                    v___y_1692_ = v___y_1711_;
                    v___y_1693_ = v___y_1713_;
                    v___y_1694_ = v___y_1716_;
                    v___y_1695_ = v___y_1715_;
                    v___y_1696_ = v___x_1727_;
                    v___y_1697_ = v___y_1718_;
                    v___y_1698_ = v_ref_1721_;
                    v___y_1699_ = v___y_1719_;
                    v___y_1700_ = v___x_1731_;
                    state = 15;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1720_);
                    v___x_1732_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_1683_ = v___x_1729_;
                    v___y_1684_ = v___y_1712_;
                    v___y_1685_ = v___y_1714_;
                    v___y_1686_ = v___x_1725_;
                    v___y_1687_ = v___y_1717_;
                    v___y_1688_ = v___x_1723_;
                    v___y_1689_ = v___x_1728_;
                    v___y_1690_ = v___x_1722_;
                    v___y_1691_ = v___y_1710_;
                    v___y_1692_ = v___y_1711_;
                    v___y_1693_ = v___y_1713_;
                    v___y_1694_ = v___y_1716_;
                    v___y_1695_ = v___y_1715_;
                    v___y_1696_ = v___x_1727_;
                    v___y_1697_ = v___y_1718_;
                    v___y_1698_ = v_ref_1721_;
                    v___y_1699_ = v___y_1719_;
                    v___y_1700_ = v___x_1732_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                v___x_1746_ = l_Lean_Syntax_getOptional_x3f(v___x_1734_);
                leanh::lean_dec(v___x_1734_);
                if leanh::lean_obj_tag(v___x_1746_) == 0 {
                    v___x_1747_ = leanh::lean_box(0);
                    v___y_1710_ = v___y_1740_;
                    v___y_1711_ = v_args_1737_;
                    v___y_1712_ = v___y_1738_;
                    v___y_1713_ = v___y_1739_;
                    v___y_1714_ = v___y_1745_;
                    v___y_1715_ = v___y_1743_;
                    v___y_1716_ = v___y_1736_;
                    v___y_1717_ = v___y_1741_;
                    v___y_1718_ = v___y_1744_;
                    v___y_1719_ = v___y_1742_;
                    v___y_1720_ = v___x_1747_;
                    state = 16;
                    continue;
                } else {
                    v_val_1748_ = leanh::lean_ctor_get(v___x_1746_, 0);
                    v_isSharedCheck_1755_ = (!leanh::lean_is_exclusive(v___x_1746_)) as u8;
                    if v_isSharedCheck_1755_ == 0 {
                        v___x_1750_ = v___x_1746_;
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1748_);
                        leanh::lean_dec(v___x_1746_);
                        v___x_1750_ = leanh::lean_box(0);
                        v_isShared_1751_ = v_isSharedCheck_1755_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_1751_ == 0 {
                    v___x_1753_ = v___x_1750_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_val_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_1710_ = v___y_1740_;
                v___y_1711_ = v_args_1737_;
                v___y_1712_ = v___y_1738_;
                v___y_1713_ = v___y_1739_;
                v___y_1714_ = v___y_1745_;
                v___y_1715_ = v___y_1743_;
                v___y_1716_ = v___y_1736_;
                v___y_1717_ = v___y_1741_;
                v___y_1718_ = v___y_1744_;
                v___y_1719_ = v___y_1742_;
                v___y_1720_ = v___x_1753_;
                state = 16;
                continue;
            }
            20 => {
                v___x_1766_ = leanh::lean_unsigned_to_nat(4);
                v___x_1767_ = l_Lean_Syntax_getArg(v_stx_1533_, v___x_1766_);
                v___x_1768_ = l_Lean_Syntax_isNone(v___x_1767_);
                if v___x_1768_ == 0 {
                    leanh::lean_inc(v___x_1767_);
                    v___x_1769_ = l_Lean_Syntax_matchesNull(v___x_1767_, v___x_1548_);
                    if v___x_1769_ == 0 {
                        leanh::lean_dec(v___x_1767_);
                        leanh::lean_dec(v_o_1757_);
                        leanh::lean_dec(v___x_1734_);
                        leanh::lean_dec(v_tk_1555_);
                        leanh::lean_dec(v___x_1549_);
                        leanh::lean_dec_ref(v___x_1536_);
                        leanh::lean_dec_ref(v___x_1535_);
                        leanh::lean_dec_ref(v___x_1534_);
                        v___x_1770_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                        return v___x_1770_;
                    } else {
                        v___x_1771_ = l_Lean_Syntax_getArg(v___x_1767_, v___x_1554_);
                        leanh::lean_dec(v___x_1767_);
                        v___x_1772_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__11;
                        leanh::lean_inc_ref(v___x_1536_);
                        leanh::lean_inc_ref(v___x_1535_);
                        leanh::lean_inc_ref(v___x_1534_);
                        v___x_1773_ =
                            l_Lean_Name_mkStr4(v___x_1534_, v___x_1535_, v___x_1536_, v___x_1772_);
                        leanh::lean_inc(v___x_1771_);
                        v___x_1774_ = l_Lean_Syntax_isOfKind(v___x_1771_, v___x_1773_);
                        leanh::lean_dec(v___x_1773_);
                        if v___x_1774_ == 0 {
                            leanh::lean_dec(v___x_1771_);
                            leanh::lean_dec(v_o_1757_);
                            leanh::lean_dec(v___x_1734_);
                            leanh::lean_dec(v_tk_1555_);
                            leanh::lean_dec(v___x_1549_);
                            leanh::lean_dec_ref(v___x_1536_);
                            leanh::lean_dec_ref(v___x_1535_);
                            leanh::lean_dec_ref(v___x_1534_);
                            v___x_1775_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                            return v___x_1775_;
                        } else {
                            v___x_1776_ = l_Lean_Syntax_getArg(v___x_1771_, v___x_1548_);
                            leanh::lean_dec(v___x_1771_);
                            v_args_1777_ = l_Lean_Syntax_getArgs(v___x_1776_);
                            leanh::lean_dec(v___x_1776_);
                            v___x_1778_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1778_, 0, v_args_1777_);
                            v___y_1736_ = v_o_1757_;
                            v_args_1737_ = v___x_1778_;
                            v___y_1738_ = v___y_1758_;
                            v___y_1739_ = v___y_1759_;
                            v___y_1740_ = v___y_1760_;
                            v___y_1741_ = v___y_1761_;
                            v___y_1742_ = v___y_1762_;
                            v___y_1743_ = v___y_1763_;
                            v___y_1744_ = v___y_1764_;
                            v___y_1745_ = v___y_1765_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1767_);
                    v___x_1779_ = leanh::lean_box(0);
                    v___y_1736_ = v_o_1757_;
                    v_args_1737_ = v___x_1779_;
                    v___y_1738_ = v___y_1758_;
                    v___y_1739_ = v___y_1759_;
                    v___y_1740_ = v___y_1760_;
                    v___y_1741_ = v___y_1761_;
                    v___y_1742_ = v___y_1762_;
                    v___y_1743_ = v___y_1763_;
                    v___y_1744_ = v___y_1764_;
                    v___y_1745_ = v___y_1765_;
                    state = 17;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed(
    mut v___x_1788_: *mut leanh::LeanObject,
    mut v_stx_1789_: *mut leanh::LeanObject,
    mut v___x_1790_: *mut leanh::LeanObject,
    mut v___x_1791_: *mut leanh::LeanObject,
    mut v___x_1792_: *mut leanh::LeanObject,
    mut v___x_1793_: *mut leanh::LeanObject,
    mut v___y_1794_: *mut leanh::LeanObject,
    mut v___y_1795_: *mut leanh::LeanObject,
    mut v___y_1796_: *mut leanh::LeanObject,
    mut v___y_1797_: *mut leanh::LeanObject,
    mut v___y_1798_: *mut leanh::LeanObject,
    mut v___y_1799_: *mut leanh::LeanObject,
    mut v___y_1800_: *mut leanh::LeanObject,
    mut v___y_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6219__boxed_1803_: u8 = 0;
    let mut v___x_6223__boxed_1804_: u8 = 0;
    let mut v_res_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6219__boxed_1803_ = (leanh::lean_unbox(v___x_1788_) as u8);
    v___x_6223__boxed_1804_ = (leanh::lean_unbox(v___x_1793_) as u8);
    v_res_1805_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1(
        v___x_6219__boxed_1803_,
        v_stx_1789_,
        v___x_1790_,
        v___x_1791_,
        v___x_1792_,
        v___x_6223__boxed_1804_,
        v___y_1794_,
        v___y_1795_,
        v___y_1796_,
        v___y_1797_,
        v___y_1798_,
        v___y_1799_,
        v___y_1800_,
        v___y_1801_,
    );
    leanh::lean_dec(v___y_1801_);
    leanh::lean_dec_ref(v___y_1800_);
    leanh::lean_dec(v___y_1799_);
    leanh::lean_dec_ref(v___y_1798_);
    leanh::lean_dec(v___y_1797_);
    leanh::lean_dec_ref(v___y_1796_);
    leanh::lean_dec(v___y_1795_);
    leanh::lean_dec_ref(v___y_1794_);
    leanh::lean_dec(v_stx_1789_);
    return v_res_1805_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace(
    mut v_stx_1813_: *mut leanh::LeanObject,
    mut v_a_1814_: *mut leanh::LeanObject,
    mut v_a_1815_: *mut leanh::LeanObject,
    mut v_a_1816_: *mut leanh::LeanObject,
    mut v_a_1817_: *mut leanh::LeanObject,
    mut v_a_1818_: *mut leanh::LeanObject,
    mut v_a_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u8 = 0;
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1823_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0;
    v___x_1824_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1;
    v___x_1825_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2;
    v___x_1826_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1;
    leanh::lean_inc(v_stx_1813_);
    v___x_1827_ = l_Lean_Syntax_isOfKind(v_stx_1813_, v___x_1826_);
    v___x_1828_ = 1;
    v___x_1829_ = leanh::lean_box((v___x_1827_) as usize);
    v___x_1830_ = leanh::lean_box((v___x_1828_) as usize);
    v___y_1831_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___boxed as *mut core::ffi::c_void,
        15,
        6,
    );
    leanh::lean_closure_set(v___y_1831_, 0, v___x_1829_);
    leanh::lean_closure_set(v___y_1831_, 1, v_stx_1813_);
    leanh::lean_closure_set(v___y_1831_, 2, v___x_1823_);
    leanh::lean_closure_set(v___y_1831_, 3, v___x_1824_);
    leanh::lean_closure_set(v___y_1831_, 4, v___x_1825_);
    leanh::lean_closure_set(v___y_1831_, 5, v___x_1830_);
    v___x_1832_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___y_1831_,
        v_a_1814_,
        v_a_1815_,
        v_a_1816_,
        v_a_1817_,
        v_a_1818_,
        v_a_1819_,
        v_a_1820_,
        v_a_1821_,
    );
    return v___x_1832_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed(
    mut v_stx_1833_: *mut leanh::LeanObject,
    mut v_a_1834_: *mut leanh::LeanObject,
    mut v_a_1835_: *mut leanh::LeanObject,
    mut v_a_1836_: *mut leanh::LeanObject,
    mut v_a_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
    mut v_a_1839_: *mut leanh::LeanObject,
    mut v_a_1840_: *mut leanh::LeanObject,
    mut v_a_1841_: *mut leanh::LeanObject,
    mut v_a_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace(
        v_stx_1833_,
        v_a_1834_,
        v_a_1835_,
        v_a_1836_,
        v_a_1837_,
        v_a_1838_,
        v_a_1839_,
        v_a_1840_,
        v_a_1841_,
    );
    leanh::lean_dec(v_a_1841_);
    leanh::lean_dec_ref(v_a_1840_);
    leanh::lean_dec(v_a_1839_);
    leanh::lean_dec_ref(v_a_1838_);
    leanh::lean_dec(v_a_1837_);
    leanh::lean_dec_ref(v_a_1836_);
    leanh::lean_dec(v_a_1835_);
    leanh::lean_dec_ref(v_a_1834_);
    return v_res_1843_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1()
-> *mut leanh::LeanObject {
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1853_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___closed__1;
    v___x_1854_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___closed__1;
    v___x_1855_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimpTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1856_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1852_,
        v___x_1853_,
        v___x_1854_,
        v___x_1855_,
    );
    return v___x_1856_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1___boxed(
    mut v_a_1857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1858_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
    return v_res_1858_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
    mut v___y_1862_: *mut leanh::LeanObject,
    mut v___y_1863_: *mut leanh::LeanObject,
    mut v___y_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut v_a_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1868_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_1860_,
                    v___y_1863_,
                    v___y_1864_,
                    v___y_1865_,
                    v___y_1866_,
                );
                if leanh::lean_obj_tag(v___x_1868_) == 0 {
                    v_a_1869_ = leanh::lean_ctor_get(v___x_1868_, 0);
                    leanh::lean_inc(v_a_1869_);
                    leanh::lean_dec_ref_known(v___x_1868_, 1);
                    v___x_1870_ = l_Lean_Meta_Split_simpMatch(
                        v_a_1869_,
                        v___y_1863_,
                        v___y_1864_,
                        v___y_1865_,
                        v___y_1866_,
                    );
                    if leanh::lean_obj_tag(v___x_1870_) == 0 {
                        v_a_1871_ = leanh::lean_ctor_get(v___x_1870_, 0);
                        leanh::lean_inc(v_a_1871_);
                        leanh::lean_dec_ref_known(v___x_1870_, 1);
                        v___x_1872_ = l_Lean_Elab_Tactic_Conv_applySimpResult(
                            v_a_1871_,
                            v___y_1859_,
                            v___y_1860_,
                            v___y_1861_,
                            v___y_1862_,
                            v___y_1863_,
                            v___y_1864_,
                            v___y_1865_,
                            v___y_1866_,
                        );
                        return v___x_1872_;
                    } else {
                        v_a_1873_ = leanh::lean_ctor_get(v___x_1870_, 0);
                        v_isSharedCheck_1880_ =
                            (!leanh::lean_is_exclusive(v___x_1870_)) as u8;
                        if v_isSharedCheck_1880_ == 0 {
                            v___x_1875_ = v___x_1870_;
                            v_isShared_1876_ = v_isSharedCheck_1880_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1873_);
                            leanh::lean_dec(v___x_1870_);
                            v___x_1875_ = leanh::lean_box(0);
                            v_isShared_1876_ = v_isSharedCheck_1880_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_1881_ = leanh::lean_ctor_get(v___x_1868_, 0);
                    v_isSharedCheck_1888_ = (!leanh::lean_is_exclusive(v___x_1868_)) as u8;
                    if v_isSharedCheck_1888_ == 0 {
                        v___x_1883_ = v___x_1868_;
                        v_isShared_1884_ = v_isSharedCheck_1888_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1881_);
                        leanh::lean_dec(v___x_1868_);
                        v___x_1883_ = leanh::lean_box(0);
                        v_isShared_1884_ = v_isSharedCheck_1888_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1876_ == 0 {
                    v___x_1878_ = v___x_1875_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1879_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
                    v___x_1878_ = v_reuseFailAlloc_1879_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1878_;
            }
            3 => {
                if v_isShared_1884_ == 0 {
                    v___x_1886_ = v___x_1883_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1887_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
                    v___x_1886_ = v_reuseFailAlloc_1887_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0___boxed(
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
    mut v___y_1894_: *mut leanh::LeanObject,
    mut v___y_1895_: *mut leanh::LeanObject,
    mut v___y_1896_: *mut leanh::LeanObject,
    mut v___y_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1898_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___lam__0(
        v___y_1889_,
        v___y_1890_,
        v___y_1891_,
        v___y_1892_,
        v___y_1893_,
        v___y_1894_,
        v___y_1895_,
        v___y_1896_,
    );
    leanh::lean_dec(v___y_1896_);
    leanh::lean_dec_ref(v___y_1895_);
    leanh::lean_dec(v___y_1894_);
    leanh::lean_dec_ref(v___y_1893_);
    leanh::lean_dec(v___y_1892_);
    leanh::lean_dec_ref(v___y_1891_);
    leanh::lean_dec(v___y_1890_);
    leanh::lean_dec_ref(v___y_1889_);
    return v_res_1898_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(
    mut v_a_1900_: *mut leanh::LeanObject,
    mut v_a_1901_: *mut leanh::LeanObject,
    mut v_a_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
    mut v_a_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
    mut v_a_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1909_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___closed__0;
    v___x_1910_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_1909_,
        v_a_1900_,
        v_a_1901_,
        v_a_1902_,
        v_a_1903_,
        v_a_1904_,
        v_a_1905_,
        v_a_1906_,
        v_a_1907_,
    );
    return v___x_1910_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg___boxed(
    mut v_a_1911_: *mut leanh::LeanObject,
    mut v_a_1912_: *mut leanh::LeanObject,
    mut v_a_1913_: *mut leanh::LeanObject,
    mut v_a_1914_: *mut leanh::LeanObject,
    mut v_a_1915_: *mut leanh::LeanObject,
    mut v_a_1916_: *mut leanh::LeanObject,
    mut v_a_1917_: *mut leanh::LeanObject,
    mut v_a_1918_: *mut leanh::LeanObject,
    mut v_a_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(
        v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_,
    );
    leanh::lean_dec(v_a_1918_);
    leanh::lean_dec_ref(v_a_1917_);
    leanh::lean_dec(v_a_1916_);
    leanh::lean_dec_ref(v_a_1915_);
    leanh::lean_dec(v_a_1914_);
    leanh::lean_dec_ref(v_a_1913_);
    leanh::lean_dec(v_a_1912_);
    leanh::lean_dec_ref(v_a_1911_);
    return v_res_1920_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch(
    mut v_x_1921_: *mut leanh::LeanObject,
    mut v_a_1922_: *mut leanh::LeanObject,
    mut v_a_1923_: *mut leanh::LeanObject,
    mut v_a_1924_: *mut leanh::LeanObject,
    mut v_a_1925_: *mut leanh::LeanObject,
    mut v_a_1926_: *mut leanh::LeanObject,
    mut v_a_1927_: *mut leanh::LeanObject,
    mut v_a_1928_: *mut leanh::LeanObject,
    mut v_a_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch___redArg(
        v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_,
    );
    return v___x_1931_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed(
    mut v_x_1932_: *mut leanh::LeanObject,
    mut v_a_1933_: *mut leanh::LeanObject,
    mut v_a_1934_: *mut leanh::LeanObject,
    mut v_a_1935_: *mut leanh::LeanObject,
    mut v_a_1936_: *mut leanh::LeanObject,
    mut v_a_1937_: *mut leanh::LeanObject,
    mut v_a_1938_: *mut leanh::LeanObject,
    mut v_a_1939_: *mut leanh::LeanObject,
    mut v_a_1940_: *mut leanh::LeanObject,
    mut v_a_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1942_ = l_Lean_Elab_Tactic_Conv_evalSimpMatch(
        v_x_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_,
        v_a_1940_,
    );
    leanh::lean_dec(v_a_1940_);
    leanh::lean_dec_ref(v_a_1939_);
    leanh::lean_dec(v_a_1938_);
    leanh::lean_dec_ref(v_a_1937_);
    leanh::lean_dec(v_a_1936_);
    leanh::lean_dec_ref(v_a_1935_);
    leanh::lean_dec(v_a_1934_);
    leanh::lean_dec_ref(v_a_1933_);
    leanh::lean_dec(v_x_1932_);
    return v_res_1942_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1()
-> *mut leanh::LeanObject {
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1959_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__1;
    v___x_1960_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3;
    v___x_1961_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalSimpMatch___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1962_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1958_,
        v___x_1959_,
        v___x_1960_,
        v___x_1961_,
    );
    return v___x_1962_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___boxed(
    mut v_a_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1964_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
    return v_res_1964_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1___closed__3;
    v___x_1992_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___closed__6;
    v___x_1993_ = l_Lean_addBuiltinDeclarationRanges(v___x_1991_, v___x_1992_);
    return v___x_1993_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3___boxed(
    mut v_a_1994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1995_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
    return v_res_1995_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(
    mut v_stx_1998_: *mut leanh::LeanObject,
    mut v___x_1999_: u8,
    mut v___x_2000_: u8,
    mut v___x_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2029_: u8 = 0;
    let mut v_a_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2033_: u8 = 0;
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_a_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2011_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v_stx_1998_,
                    v___x_1999_,
                    v___x_2000_,
                    v___x_1999_,
                    v___x_2001_,
                    v___y_2002_,
                    v___y_2003_,
                    v___y_2004_,
                    v___y_2005_,
                    v___y_2006_,
                    v___y_2007_,
                    v___y_2008_,
                    v___y_2009_,
                );
                if leanh::lean_obj_tag(v___x_2011_) == 0 {
                    v_a_2012_ = leanh::lean_ctor_get(v___x_2011_, 0);
                    leanh::lean_inc(v_a_2012_);
                    leanh::lean_dec_ref_known(v___x_2011_, 1);
                    v_ctx_2013_ = leanh::lean_ctor_get(v_a_2012_, 0);
                    leanh::lean_inc_ref(v_ctx_2013_);
                    leanh::lean_dec(v_a_2012_);
                    v___x_2014_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_2003_,
                        v___y_2006_,
                        v___y_2007_,
                        v___y_2008_,
                        v___y_2009_,
                    );
                    if leanh::lean_obj_tag(v___x_2014_) == 0 {
                        v_a_2015_ = leanh::lean_ctor_get(v___x_2014_, 0);
                        leanh::lean_inc(v_a_2015_);
                        leanh::lean_dec_ref_known(v___x_2014_, 1);
                        v___x_2016_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0;
                        v___x_2017_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6,
                        );
                        v___x_2018_ = l_Lean_Meta_dsimp(
                            v_a_2015_,
                            v_ctx_2013_,
                            v___x_2016_,
                            v___x_2017_,
                            v___y_2006_,
                            v___y_2007_,
                            v___y_2008_,
                            v___y_2009_,
                        );
                        if leanh::lean_obj_tag(v___x_2018_) == 0 {
                            v_a_2019_ = leanh::lean_ctor_get(v___x_2018_, 0);
                            leanh::lean_inc(v_a_2019_);
                            leanh::lean_dec_ref_known(v___x_2018_, 1);
                            v_fst_2020_ = leanh::lean_ctor_get(v_a_2019_, 0);
                            leanh::lean_inc(v_fst_2020_);
                            leanh::lean_dec(v_a_2019_);
                            v___x_2021_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_fst_2020_,
                                v___y_2002_,
                                v___y_2003_,
                                v___y_2004_,
                                v___y_2005_,
                                v___y_2006_,
                                v___y_2007_,
                                v___y_2008_,
                                v___y_2009_,
                            );
                            return v___x_2021_;
                        } else {
                            v_a_2022_ = leanh::lean_ctor_get(v___x_2018_, 0);
                            v_isSharedCheck_2029_ =
                                (!leanh::lean_is_exclusive(v___x_2018_)) as u8;
                            if v_isSharedCheck_2029_ == 0 {
                                v___x_2024_ = v___x_2018_;
                                v_isShared_2025_ = v_isSharedCheck_2029_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2022_);
                                leanh::lean_dec(v___x_2018_);
                                v___x_2024_ = leanh::lean_box(0);
                                v_isShared_2025_ = v_isSharedCheck_2029_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_ctx_2013_);
                        v_a_2030_ = leanh::lean_ctor_get(v___x_2014_, 0);
                        v_isSharedCheck_2037_ =
                            (!leanh::lean_is_exclusive(v___x_2014_)) as u8;
                        if v_isSharedCheck_2037_ == 0 {
                            v___x_2032_ = v___x_2014_;
                            v_isShared_2033_ = v_isSharedCheck_2037_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2030_);
                            leanh::lean_dec(v___x_2014_);
                            v___x_2032_ = leanh::lean_box(0);
                            v_isShared_2033_ = v_isSharedCheck_2037_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2038_ = leanh::lean_ctor_get(v___x_2011_, 0);
                    v_isSharedCheck_2045_ = (!leanh::lean_is_exclusive(v___x_2011_)) as u8;
                    if v_isSharedCheck_2045_ == 0 {
                        v___x_2040_ = v___x_2011_;
                        v_isShared_2041_ = v_isSharedCheck_2045_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2038_);
                        leanh::lean_dec(v___x_2011_);
                        v___x_2040_ = leanh::lean_box(0);
                        v_isShared_2041_ = v_isSharedCheck_2045_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2025_ == 0 {
                    v___x_2027_ = v___x_2024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2028_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
                    v___x_2027_ = v_reuseFailAlloc_2028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2027_;
            }
            3 => {
                if v_isShared_2033_ == 0 {
                    v___x_2035_ = v___x_2032_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2036_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
                    v___x_2035_ = v_reuseFailAlloc_2036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2035_;
            }
            5 => {
                if v_isShared_2041_ == 0 {
                    v___x_2043_ = v___x_2040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
                    v___x_2043_ = v_reuseFailAlloc_2044_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed(
    mut v_stx_2046_: *mut leanh::LeanObject,
    mut v___x_2047_: *mut leanh::LeanObject,
    mut v___x_2048_: *mut leanh::LeanObject,
    mut v___x_2049_: *mut leanh::LeanObject,
    mut v___y_2050_: *mut leanh::LeanObject,
    mut v___y_2051_: *mut leanh::LeanObject,
    mut v___y_2052_: *mut leanh::LeanObject,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
    mut v___y_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_586__boxed_2059_: u8 = 0;
    let mut v___x_587__boxed_2060_: u8 = 0;
    let mut v_res_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_586__boxed_2059_ = (leanh::lean_unbox(v___x_2047_) as u8);
    v___x_587__boxed_2060_ = (leanh::lean_unbox(v___x_2048_) as u8);
    v_res_2061_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0(
        v_stx_2046_,
        v___x_586__boxed_2059_,
        v___x_587__boxed_2060_,
        v___x_2049_,
        v___y_2050_,
        v___y_2051_,
        v___y_2052_,
        v___y_2053_,
        v___y_2054_,
        v___y_2055_,
        v___y_2056_,
        v___y_2057_,
    );
    leanh::lean_dec(v___y_2057_);
    leanh::lean_dec_ref(v___y_2056_);
    leanh::lean_dec(v___y_2055_);
    leanh::lean_dec_ref(v___y_2054_);
    leanh::lean_dec(v___y_2053_);
    leanh::lean_dec_ref(v___y_2052_);
    leanh::lean_dec(v___y_2051_);
    leanh::lean_dec_ref(v___y_2050_);
    leanh::lean_dec(v_stx_2046_);
    return v_res_2061_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimp(
    mut v_stx_2062_: *mut leanh::LeanObject,
    mut v_a_2063_: *mut leanh::LeanObject,
    mut v_a_2064_: *mut leanh::LeanObject,
    mut v_a_2065_: *mut leanh::LeanObject,
    mut v_a_2066_: *mut leanh::LeanObject,
    mut v_a_2067_: *mut leanh::LeanObject,
    mut v_a_2068_: *mut leanh::LeanObject,
    mut v_a_2069_: *mut leanh::LeanObject,
    mut v_a_2070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: u8 = 0;
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = 0;
    v___x_2073_ = 2;
    v___x_2074_ = l_Lean_Elab_Tactic_Conv_evalSimp___closed__0;
    v___x_2075_ = leanh::lean_box((v___x_2072_) as usize);
    v___x_2076_ = leanh::lean_box((v___x_2073_) as usize);
    v___f_2077_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    leanh::lean_closure_set(v___f_2077_, 0, v_stx_2062_);
    leanh::lean_closure_set(v___f_2077_, 1, v___x_2075_);
    leanh::lean_closure_set(v___f_2077_, 2, v___x_2076_);
    leanh::lean_closure_set(v___f_2077_, 3, v___x_2074_);
    v___x_2078_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_2077_,
        v_a_2063_,
        v_a_2064_,
        v_a_2065_,
        v_a_2066_,
        v_a_2067_,
        v_a_2068_,
        v_a_2069_,
        v_a_2070_,
    );
    return v___x_2078_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimp___boxed(
    mut v_stx_2079_: *mut leanh::LeanObject,
    mut v_a_2080_: *mut leanh::LeanObject,
    mut v_a_2081_: *mut leanh::LeanObject,
    mut v_a_2082_: *mut leanh::LeanObject,
    mut v_a_2083_: *mut leanh::LeanObject,
    mut v_a_2084_: *mut leanh::LeanObject,
    mut v_a_2085_: *mut leanh::LeanObject,
    mut v_a_2086_: *mut leanh::LeanObject,
    mut v_a_2087_: *mut leanh::LeanObject,
    mut v_a_2088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l_Lean_Elab_Tactic_Conv_evalDSimp(
        v_stx_2079_,
        v_a_2080_,
        v_a_2081_,
        v_a_2082_,
        v_a_2083_,
        v_a_2084_,
        v_a_2085_,
        v_a_2086_,
        v_a_2087_,
    );
    leanh::lean_dec(v_a_2087_);
    leanh::lean_dec_ref(v_a_2086_);
    leanh::lean_dec(v_a_2085_);
    leanh::lean_dec_ref(v_a_2084_);
    leanh::lean_dec(v_a_2083_);
    leanh::lean_dec_ref(v_a_2082_);
    leanh::lean_dec(v_a_2081_);
    leanh::lean_dec_ref(v_a_2080_);
    return v_res_2089_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1()
-> *mut leanh::LeanObject {
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2105_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2106_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__1;
    v___x_2107_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3;
    v___x_2108_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDSimp___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2109_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2105_,
        v___x_2106_,
        v___x_2107_,
        v___x_2108_,
    );
    return v___x_2109_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___boxed(
    mut v_a_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2111_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
    return v_res_2111_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__3;
    v___x_2138_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___closed__6;
    v___x_2139_ = l_Lean_addBuiltinDeclarationRanges(v___x_2137_, v___x_2138_);
    return v___x_2139_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3___boxed(
    mut v_a_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
    return v_res_2141_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(
    mut v___x_2143_: u8,
    mut v_stx_2144_: *mut leanh::LeanObject,
    mut v___x_2145_: *mut leanh::LeanObject,
    mut v___x_2146_: *mut leanh::LeanObject,
    mut v___x_2147_: *mut leanh::LeanObject,
    mut v___x_2148_: u8,
    mut v___y_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
    mut v___y_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
    mut v___y_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: u8 = 0;
    let mut v___y_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v_usedTheorems_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2209_: u8 = 0;
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2232_: u8 = 0;
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v_unused_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v_unused_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_a_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut v_a_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2256_: u8 = 0;
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v___y_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2265_: u8 = 0;
    let mut v___y_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_o_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_o_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_2143_ == 0 {
                    leanh::lean_dec_ref(v___x_2147_);
                    leanh::lean_dec_ref(v___x_2146_);
                    leanh::lean_dec_ref(v___x_2145_);
                    v___x_2158_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                    return v___x_2158_;
                } else {
                    v___x_2159_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2160_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2159_);
                    v___x_2161_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__0;
                    leanh::lean_inc_ref(v___x_2147_);
                    leanh::lean_inc_ref(v___x_2146_);
                    leanh::lean_inc_ref(v___x_2145_);
                    v___x_2162_ =
                        l_Lean_Name_mkStr4(v___x_2145_, v___x_2146_, v___x_2147_, v___x_2161_);
                    leanh::lean_inc(v___x_2160_);
                    v___x_2163_ = l_Lean_Syntax_isOfKind(v___x_2160_, v___x_2162_);
                    leanh::lean_dec(v___x_2162_);
                    if v___x_2163_ == 0 {
                        leanh::lean_dec(v___x_2160_);
                        leanh::lean_dec_ref(v___x_2147_);
                        leanh::lean_dec_ref(v___x_2146_);
                        leanh::lean_dec_ref(v___x_2145_);
                        v___x_2164_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                        return v___x_2164_;
                    } else {
                        v___x_2165_ = leanh::lean_unsigned_to_nat(0);
                        v_tk_2166_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2165_);
                        v___x_2342_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2343_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2342_);
                        v___x_2344_ = l_Lean_Syntax_isNone(v___x_2343_);
                        if v___x_2344_ == 0 {
                            leanh::lean_inc(v___x_2343_);
                            v___x_2345_ = l_Lean_Syntax_matchesNull(v___x_2343_, v___x_2159_);
                            if v___x_2345_ == 0 {
                                leanh::lean_dec(v___x_2343_);
                                leanh::lean_dec(v_tk_2166_);
                                leanh::lean_dec(v___x_2160_);
                                leanh::lean_dec_ref(v___x_2147_);
                                leanh::lean_dec_ref(v___x_2146_);
                                leanh::lean_dec_ref(v___x_2145_);
                                v___x_2346_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                                return v___x_2346_;
                            } else {
                                v_o_2347_ = l_Lean_Syntax_getArg(v___x_2343_, v___x_2165_);
                                leanh::lean_dec(v___x_2343_);
                                v___x_2348_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2348_, 0, v_o_2347_);
                                v_o_2319_ = v___x_2348_;
                                v___y_2320_ = v___y_2149_;
                                v___y_2321_ = v___y_2150_;
                                v___y_2322_ = v___y_2151_;
                                v___y_2323_ = v___y_2152_;
                                v___y_2324_ = v___y_2153_;
                                v___y_2325_ = v___y_2154_;
                                v___y_2326_ = v___y_2155_;
                                v___y_2327_ = v___y_2156_;
                                state = 16;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2343_);
                            v___x_2349_ = leanh::lean_box(0);
                            v_o_2319_ = v___x_2349_;
                            v___y_2320_ = v___y_2149_;
                            v___y_2321_ = v___y_2150_;
                            v___y_2322_ = v___y_2151_;
                            v___y_2323_ = v___y_2152_;
                            v___y_2324_ = v___y_2153_;
                            v___y_2325_ = v___y_2154_;
                            v___y_2326_ = v___y_2155_;
                            v___y_2327_ = v___y_2156_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_2177_);
                v___x_2186_ = l_Array_append___redArg(v___y_2177_, v___y_2185_);
                leanh::lean_dec_ref(v___y_2185_);
                leanh::lean_inc(v___y_2180_);
                leanh::lean_inc(v___y_2182_);
                v___x_2187_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2187_, 0, v___y_2182_);
                leanh::lean_ctor_set(v___x_2187_, 1, v___y_2180_);
                leanh::lean_ctor_set(v___x_2187_, 2, v___x_2186_);
                leanh::lean_inc(v___y_2171_);
                v___x_2188_ = l_Lean_Syntax_node6(
                    v___y_2182_,
                    v___y_2176_,
                    v___y_2184_,
                    v___x_2160_,
                    v___y_2171_,
                    v___y_2168_,
                    v___x_2187_,
                    v___y_2171_,
                );
                v___x_2189_ = 2;
                v___x_2190_ = l_Lean_Elab_Tactic_Conv_evalSimp___closed__0;
                v___x_2191_ = l_Lean_Elab_Tactic_mkSimpContext(
                    v___x_2188_,
                    v___y_2172_,
                    v___x_2189_,
                    v___y_2172_,
                    v___x_2190_,
                    v___y_2181_,
                    v___y_2179_,
                    v___y_2169_,
                    v___y_2173_,
                    v___y_2178_,
                    v___y_2175_,
                    v___y_2183_,
                    v___y_2174_,
                );
                if leanh::lean_obj_tag(v___x_2191_) == 0 {
                    v_a_2192_ = leanh::lean_ctor_get(v___x_2191_, 0);
                    leanh::lean_inc(v_a_2192_);
                    leanh::lean_dec_ref_known(v___x_2191_, 1);
                    v_ctx_2193_ = leanh::lean_ctor_get(v_a_2192_, 0);
                    leanh::lean_inc_ref(v_ctx_2193_);
                    leanh::lean_dec(v_a_2192_);
                    v___x_2194_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_2179_,
                        v___y_2178_,
                        v___y_2175_,
                        v___y_2183_,
                        v___y_2174_,
                    );
                    if leanh::lean_obj_tag(v___x_2194_) == 0 {
                        v_a_2195_ = leanh::lean_ctor_get(v___x_2194_, 0);
                        leanh::lean_inc(v_a_2195_);
                        leanh::lean_dec_ref_known(v___x_2194_, 1);
                        v___x_2196_ = l_Lean_Elab_Tactic_Conv_evalDSimp___lam__0___closed__0;
                        v___x_2197_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalSimp___lam__0___closed__6,
                        );
                        v___x_2198_ = l_Lean_Meta_dsimp(
                            v_a_2195_,
                            v_ctx_2193_,
                            v___x_2196_,
                            v___x_2197_,
                            v___y_2178_,
                            v___y_2175_,
                            v___y_2183_,
                            v___y_2174_,
                        );
                        if leanh::lean_obj_tag(v___x_2198_) == 0 {
                            v_a_2199_ = leanh::lean_ctor_get(v___x_2198_, 0);
                            leanh::lean_inc(v_a_2199_);
                            leanh::lean_dec_ref_known(v___x_2198_, 1);
                            v_fst_2200_ = leanh::lean_ctor_get(v_a_2199_, 0);
                            leanh::lean_inc(v_fst_2200_);
                            v_snd_2201_ = leanh::lean_ctor_get(v_a_2199_, 1);
                            leanh::lean_inc(v_snd_2201_);
                            leanh::lean_dec(v_a_2199_);
                            v___x_2202_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_fst_2200_,
                                v___y_2181_,
                                v___y_2179_,
                                v___y_2169_,
                                v___y_2173_,
                                v___y_2178_,
                                v___y_2175_,
                                v___y_2183_,
                                v___y_2174_,
                            );
                            if leanh::lean_obj_tag(v___x_2202_) == 0 {
                                v_isSharedCheck_2235_ =
                                    (!leanh::lean_is_exclusive(v___x_2202_)) as u8;
                                if v_isSharedCheck_2235_ == 0 {
                                    v_unused_2236_ = leanh::lean_ctor_get(v___x_2202_, 0);
                                    leanh::lean_dec(v_unused_2236_);
                                    v___x_2204_ = v___x_2202_;
                                    v_isShared_2205_ = v_isSharedCheck_2235_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_2202_);
                                    v___x_2204_ = leanh::lean_box(0);
                                    v_isShared_2205_ = v_isSharedCheck_2235_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_snd_2201_);
                                leanh::lean_dec(v___x_2188_);
                                leanh::lean_dec(v_tk_2166_);
                                return v___x_2202_;
                            }
                        } else {
                            leanh::lean_dec(v___x_2188_);
                            leanh::lean_dec(v_tk_2166_);
                            v_a_2237_ = leanh::lean_ctor_get(v___x_2198_, 0);
                            v_isSharedCheck_2244_ =
                                (!leanh::lean_is_exclusive(v___x_2198_)) as u8;
                            if v_isSharedCheck_2244_ == 0 {
                                v___x_2239_ = v___x_2198_;
                                v_isShared_2240_ = v_isSharedCheck_2244_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2237_);
                                leanh::lean_dec(v___x_2198_);
                                v___x_2239_ = leanh::lean_box(0);
                                v_isShared_2240_ = v_isSharedCheck_2244_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_ctx_2193_);
                        leanh::lean_dec(v___x_2188_);
                        leanh::lean_dec(v_tk_2166_);
                        v_a_2245_ = leanh::lean_ctor_get(v___x_2194_, 0);
                        v_isSharedCheck_2252_ =
                            (!leanh::lean_is_exclusive(v___x_2194_)) as u8;
                        if v_isSharedCheck_2252_ == 0 {
                            v___x_2247_ = v___x_2194_;
                            v_isShared_2248_ = v_isSharedCheck_2252_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2245_);
                            leanh::lean_dec(v___x_2194_);
                            v___x_2247_ = leanh::lean_box(0);
                            v_isShared_2248_ = v_isSharedCheck_2252_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2188_);
                    leanh::lean_dec(v_tk_2166_);
                    v_a_2253_ = leanh::lean_ctor_get(v___x_2191_, 0);
                    v_isSharedCheck_2260_ = (!leanh::lean_is_exclusive(v___x_2191_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v___x_2255_ = v___x_2191_;
                        v_isShared_2256_ = v_isSharedCheck_2260_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2253_);
                        leanh::lean_dec(v___x_2191_);
                        v___x_2255_ = leanh::lean_box(0);
                        v_isShared_2256_ = v_isSharedCheck_2260_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_usedTheorems_2206_ = leanh::lean_ctor_get(v_snd_2201_, 0);
                v_isSharedCheck_2233_ = (!leanh::lean_is_exclusive(v_snd_2201_)) as u8;
                if v_isSharedCheck_2233_ == 0 {
                    v_unused_2234_ = leanh::lean_ctor_get(v_snd_2201_, 1);
                    leanh::lean_dec(v_unused_2234_);
                    v___x_2208_ = v_snd_2201_;
                    v_isShared_2209_ = v_isSharedCheck_2233_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_usedTheorems_2206_);
                    leanh::lean_dec(v_snd_2201_);
                    v___x_2208_ = leanh::lean_box(0);
                    v_isShared_2209_ = v_isSharedCheck_2233_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2210_ = l_Lean_Elab_Tactic_mkSimpCallStx(
                    v___x_2188_,
                    v_usedTheorems_2206_,
                    v___y_2178_,
                    v___y_2175_,
                    v___y_2183_,
                    v___y_2174_,
                );
                leanh::lean_dec_ref(v_usedTheorems_2206_);
                if leanh::lean_obj_tag(v___x_2210_) == 0 {
                    v_a_2211_ = leanh::lean_ctor_get(v___x_2210_, 0);
                    leanh::lean_inc(v_a_2211_);
                    leanh::lean_dec_ref_known(v___x_2210_, 1);
                    v___x_2212_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__2;
                    if v_isShared_2209_ == 0 {
                        leanh::lean_ctor_set(v___x_2208_, 1, v_a_2211_);
                        leanh::lean_ctor_set(v___x_2208_, 0, v___x_2212_);
                        v___x_2214_ = v___x_2208_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2212_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_a_2211_);
                        v___x_2214_ = v_reuseFailAlloc_2224_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2208_);
                    leanh::lean_del_object(v___x_2204_);
                    leanh::lean_dec(v_tk_2166_);
                    v_a_2225_ = leanh::lean_ctor_get(v___x_2210_, 0);
                    v_isSharedCheck_2232_ = (!leanh::lean_is_exclusive(v___x_2210_)) as u8;
                    if v_isSharedCheck_2232_ == 0 {
                        v___x_2227_ = v___x_2210_;
                        v_isShared_2228_ = v_isSharedCheck_2232_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2225_);
                        leanh::lean_dec(v___x_2210_);
                        v___x_2227_ = leanh::lean_box(0);
                        v_isShared_2228_ = v_isSharedCheck_2232_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2215_ = leanh::lean_box(0);
                v___x_2216_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_2216_, 0, v___x_2214_);
                leanh::lean_ctor_set(v___x_2216_, 1, v___x_2215_);
                leanh::lean_ctor_set(v___x_2216_, 2, v___x_2215_);
                leanh::lean_ctor_set(v___x_2216_, 3, v___x_2215_);
                leanh::lean_ctor_set(v___x_2216_, 4, v___x_2215_);
                leanh::lean_ctor_set(v___x_2216_, 5, v___x_2215_);
                leanh::lean_inc(v___y_2170_);
                if v_isShared_2205_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2204_, 1);
                    leanh::lean_ctor_set(v___x_2204_, 0, v___y_2170_);
                    v___x_2218_ = v___x_2204_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2223_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___y_2170_);
                    v___x_2218_ = v_reuseFailAlloc_2223_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2219_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__3;
                v___x_2220_ = 4;
                v___x_2221_ = l_Lean_MessageData_nil;
                v___x_2222_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_2166_,
                    v___x_2216_,
                    v___x_2218_,
                    v___x_2219_,
                    v___x_2215_,
                    v___x_2220_,
                    v___x_2221_,
                    v___y_2183_,
                    v___y_2174_,
                );
                return v___x_2222_;
            }
            6 => {
                if v_isShared_2228_ == 0 {
                    v___x_2230_ = v___x_2227_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2231_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
                    v___x_2230_ = v_reuseFailAlloc_2231_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2230_;
            }
            8 => {
                if v_isShared_2240_ == 0 {
                    v___x_2242_ = v___x_2239_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
                    v___x_2242_ = v_reuseFailAlloc_2243_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2242_;
            }
            10 => {
                if v_isShared_2248_ == 0 {
                    v___x_2250_ = v___x_2247_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
                    v___x_2250_ = v_reuseFailAlloc_2251_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2250_;
            }
            12 => {
                if v_isShared_2256_ == 0 {
                    v___x_2258_ = v___x_2255_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
                    v___x_2258_ = v_reuseFailAlloc_2259_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2258_;
            }
            14 => {
                leanh::lean_inc_ref(v___y_2270_);
                v___x_2280_ = l_Array_append___redArg(v___y_2270_, v___y_2279_);
                leanh::lean_dec_ref(v___y_2279_);
                leanh::lean_inc(v___y_2273_);
                leanh::lean_inc(v___y_2276_);
                v___x_2281_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2281_, 0, v___y_2276_);
                leanh::lean_ctor_set(v___x_2281_, 1, v___y_2273_);
                leanh::lean_ctor_set(v___x_2281_, 2, v___x_2280_);
                if leanh::lean_obj_tag(v___y_2275_) == 1 {
                    v_val_2282_ = leanh::lean_ctor_get(v___y_2275_, 0);
                    leanh::lean_inc(v_val_2282_);
                    leanh::lean_dec_ref_known(v___y_2275_, 1);
                    v___x_2283_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__4;
                    leanh::lean_inc_n(v___y_2276_, 3);
                    v___x_2284_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2284_, 0, v___y_2276_);
                    leanh::lean_ctor_set(v___x_2284_, 1, v___x_2283_);
                    leanh::lean_inc_ref(v___y_2270_);
                    v___x_2285_ = l_Array_append___redArg(v___y_2270_, v_val_2282_);
                    leanh::lean_dec(v_val_2282_);
                    leanh::lean_inc(v___y_2273_);
                    v___x_2286_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2286_, 0, v___y_2276_);
                    leanh::lean_ctor_set(v___x_2286_, 1, v___y_2273_);
                    leanh::lean_ctor_set(v___x_2286_, 2, v___x_2285_);
                    v___x_2287_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__5;
                    v___x_2288_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2288_, 0, v___y_2276_);
                    leanh::lean_ctor_set(v___x_2288_, 1, v___x_2287_);
                    v___x_2289_ = l_Array_mkArray3___redArg(v___x_2284_, v___x_2286_, v___x_2288_);
                    v___y_2168_ = v___x_2281_;
                    v___y_2169_ = v___y_2262_;
                    v___y_2170_ = v___y_2263_;
                    v___y_2171_ = v___y_2264_;
                    v___y_2172_ = v___y_2265_;
                    v___y_2173_ = v___y_2266_;
                    v___y_2174_ = v___y_2267_;
                    v___y_2175_ = v___y_2268_;
                    v___y_2176_ = v___y_2269_;
                    v___y_2177_ = v___y_2270_;
                    v___y_2178_ = v___y_2271_;
                    v___y_2179_ = v___y_2272_;
                    v___y_2180_ = v___y_2273_;
                    v___y_2181_ = v___y_2274_;
                    v___y_2182_ = v___y_2276_;
                    v___y_2183_ = v___y_2278_;
                    v___y_2184_ = v___y_2277_;
                    v___y_2185_ = v___x_2289_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_2275_);
                    v___x_2290_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_2168_ = v___x_2281_;
                    v___y_2169_ = v___y_2262_;
                    v___y_2170_ = v___y_2263_;
                    v___y_2171_ = v___y_2264_;
                    v___y_2172_ = v___y_2265_;
                    v___y_2173_ = v___y_2266_;
                    v___y_2174_ = v___y_2267_;
                    v___y_2175_ = v___y_2268_;
                    v___y_2176_ = v___y_2269_;
                    v___y_2177_ = v___y_2270_;
                    v___y_2178_ = v___y_2271_;
                    v___y_2179_ = v___y_2272_;
                    v___y_2180_ = v___y_2273_;
                    v___y_2181_ = v___y_2274_;
                    v___y_2182_ = v___y_2276_;
                    v___y_2183_ = v___y_2278_;
                    v___y_2184_ = v___y_2277_;
                    v___y_2185_ = v___x_2290_;
                    state = 1;
                    continue;
                }
            }
            15 => {
                v_ref_2302_ = leanh::lean_ctor_get(v___y_2300_, 5);
                v___x_2303_ = 0;
                v___x_2304_ = l_Lean_SourceInfo_fromRef(v_ref_2302_, v___x_2303_);
                v___x_2305_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1___closed__0;
                v___x_2306_ =
                    l_Lean_Name_mkStr4(v___x_2145_, v___x_2146_, v___x_2147_, v___x_2305_);
                v___x_2307_ = l_Lean_SourceInfo_fromRef(v_tk_2166_, v___x_2148_);
                v___x_2308_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                leanh::lean_ctor_set(v___x_2308_, 1, v___x_2305_);
                v___x_2309_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__9;
                v___x_2310_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__10,
                );
                leanh::lean_inc(v___x_2304_);
                v___x_2311_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2311_, 0, v___x_2304_);
                leanh::lean_ctor_set(v___x_2311_, 1, v___x_2309_);
                leanh::lean_ctor_set(v___x_2311_, 2, v___x_2310_);
                if leanh::lean_obj_tag(v___y_2292_) == 1 {
                    v_val_2312_ = leanh::lean_ctor_get(v___y_2292_, 0);
                    leanh::lean_inc(v_val_2312_);
                    leanh::lean_dec_ref_known(v___y_2292_, 1);
                    v___x_2313_ = l_Lean_SourceInfo_fromRef(v_val_2312_, v___x_2148_);
                    leanh::lean_dec(v_val_2312_);
                    v___x_2314_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__7;
                    v___x_2315_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2315_, 0, v___x_2313_);
                    leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                    v___x_2316_ = l_Array_mkArray1___redArg(v___x_2315_);
                    v___y_2262_ = v___y_2296_;
                    v___y_2263_ = v_ref_2302_;
                    v___y_2264_ = v___x_2311_;
                    v___y_2265_ = v___x_2303_;
                    v___y_2266_ = v___y_2297_;
                    v___y_2267_ = v___y_2301_;
                    v___y_2268_ = v___y_2299_;
                    v___y_2269_ = v___x_2306_;
                    v___y_2270_ = v___x_2310_;
                    v___y_2271_ = v___y_2298_;
                    v___y_2272_ = v___y_2295_;
                    v___y_2273_ = v___x_2309_;
                    v___y_2274_ = v___y_2294_;
                    v___y_2275_ = v_args_2293_;
                    v___y_2276_ = v___x_2304_;
                    v___y_2277_ = v___x_2308_;
                    v___y_2278_ = v___y_2300_;
                    v___y_2279_ = v___x_2316_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_dec(v___y_2292_);
                    v___x_2317_ = l_Lean_Elab_Tactic_Conv_evalSimpTrace___lam__1___closed__6;
                    v___y_2262_ = v___y_2296_;
                    v___y_2263_ = v_ref_2302_;
                    v___y_2264_ = v___x_2311_;
                    v___y_2265_ = v___x_2303_;
                    v___y_2266_ = v___y_2297_;
                    v___y_2267_ = v___y_2301_;
                    v___y_2268_ = v___y_2299_;
                    v___y_2269_ = v___x_2306_;
                    v___y_2270_ = v___x_2310_;
                    v___y_2271_ = v___y_2298_;
                    v___y_2272_ = v___y_2295_;
                    v___y_2273_ = v___x_2309_;
                    v___y_2274_ = v___y_2294_;
                    v___y_2275_ = v_args_2293_;
                    v___y_2276_ = v___x_2304_;
                    v___y_2277_ = v___x_2308_;
                    v___y_2278_ = v___y_2300_;
                    v___y_2279_ = v___x_2317_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v___x_2328_ = leanh::lean_unsigned_to_nat(3);
                v___x_2329_ = l_Lean_Syntax_getArg(v_stx_2144_, v___x_2328_);
                v___x_2330_ = l_Lean_Syntax_isNone(v___x_2329_);
                if v___x_2330_ == 0 {
                    leanh::lean_inc(v___x_2329_);
                    v___x_2331_ = l_Lean_Syntax_matchesNull(v___x_2329_, v___x_2159_);
                    if v___x_2331_ == 0 {
                        leanh::lean_dec(v___x_2329_);
                        leanh::lean_dec(v_o_2319_);
                        leanh::lean_dec(v_tk_2166_);
                        leanh::lean_dec(v___x_2160_);
                        leanh::lean_dec_ref(v___x_2147_);
                        leanh::lean_dec_ref(v___x_2146_);
                        leanh::lean_dec_ref(v___x_2145_);
                        v___x_2332_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                        return v___x_2332_;
                    } else {
                        v___x_2333_ = l_Lean_Syntax_getArg(v___x_2329_, v___x_2165_);
                        leanh::lean_dec(v___x_2329_);
                        v___x_2334_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___closed__0;
                        leanh::lean_inc_ref(v___x_2147_);
                        leanh::lean_inc_ref(v___x_2146_);
                        leanh::lean_inc_ref(v___x_2145_);
                        v___x_2335_ =
                            l_Lean_Name_mkStr4(v___x_2145_, v___x_2146_, v___x_2147_, v___x_2334_);
                        leanh::lean_inc(v___x_2333_);
                        v___x_2336_ = l_Lean_Syntax_isOfKind(v___x_2333_, v___x_2335_);
                        leanh::lean_dec(v___x_2335_);
                        if v___x_2336_ == 0 {
                            leanh::lean_dec(v___x_2333_);
                            leanh::lean_dec(v_o_2319_);
                            leanh::lean_dec(v_tk_2166_);
                            leanh::lean_dec(v___x_2160_);
                            leanh::lean_dec_ref(v___x_2147_);
                            leanh::lean_dec_ref(v___x_2146_);
                            leanh::lean_dec_ref(v___x_2145_);
                            v___x_2337_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalSimpTrace_spec__0___redArg();
                            return v___x_2337_;
                        } else {
                            v___x_2338_ = l_Lean_Syntax_getArg(v___x_2333_, v___x_2159_);
                            leanh::lean_dec(v___x_2333_);
                            v_args_2339_ = l_Lean_Syntax_getArgs(v___x_2338_);
                            leanh::lean_dec(v___x_2338_);
                            v___x_2340_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2340_, 0, v_args_2339_);
                            v___y_2292_ = v_o_2319_;
                            v_args_2293_ = v___x_2340_;
                            v___y_2294_ = v___y_2320_;
                            v___y_2295_ = v___y_2321_;
                            v___y_2296_ = v___y_2322_;
                            v___y_2297_ = v___y_2323_;
                            v___y_2298_ = v___y_2324_;
                            v___y_2299_ = v___y_2325_;
                            v___y_2300_ = v___y_2326_;
                            v___y_2301_ = v___y_2327_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2329_);
                    v___x_2341_ = leanh::lean_box(0);
                    v___y_2292_ = v_o_2319_;
                    v_args_2293_ = v___x_2341_;
                    v___y_2294_ = v___y_2320_;
                    v___y_2295_ = v___y_2321_;
                    v___y_2296_ = v___y_2322_;
                    v___y_2297_ = v___y_2323_;
                    v___y_2298_ = v___y_2324_;
                    v___y_2299_ = v___y_2325_;
                    v___y_2300_ = v___y_2326_;
                    v___y_2301_ = v___y_2327_;
                    state = 15;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed(
    mut v___x_2350_: *mut leanh::LeanObject,
    mut v_stx_2351_: *mut leanh::LeanObject,
    mut v___x_2352_: *mut leanh::LeanObject,
    mut v___x_2353_: *mut leanh::LeanObject,
    mut v___x_2354_: *mut leanh::LeanObject,
    mut v___x_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
    mut v___y_2358_: *mut leanh::LeanObject,
    mut v___y_2359_: *mut leanh::LeanObject,
    mut v___y_2360_: *mut leanh::LeanObject,
    mut v___y_2361_: *mut leanh::LeanObject,
    mut v___y_2362_: *mut leanh::LeanObject,
    mut v___y_2363_: *mut leanh::LeanObject,
    mut v___y_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5500__boxed_2365_: u8 = 0;
    let mut v___x_5504__boxed_2366_: u8 = 0;
    let mut v_res_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5500__boxed_2365_ = (leanh::lean_unbox(v___x_2350_) as u8);
    v___x_5504__boxed_2366_ = (leanh::lean_unbox(v___x_2355_) as u8);
    v_res_2367_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0(
        v___x_5500__boxed_2365_,
        v_stx_2351_,
        v___x_2352_,
        v___x_2353_,
        v___x_2354_,
        v___x_5504__boxed_2366_,
        v___y_2356_,
        v___y_2357_,
        v___y_2358_,
        v___y_2359_,
        v___y_2360_,
        v___y_2361_,
        v___y_2362_,
        v___y_2363_,
    );
    leanh::lean_dec(v___y_2363_);
    leanh::lean_dec_ref(v___y_2362_);
    leanh::lean_dec(v___y_2361_);
    leanh::lean_dec_ref(v___y_2360_);
    leanh::lean_dec(v___y_2359_);
    leanh::lean_dec_ref(v___y_2358_);
    leanh::lean_dec(v___y_2357_);
    leanh::lean_dec_ref(v___y_2356_);
    leanh::lean_dec(v_stx_2351_);
    return v_res_2367_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimpTrace(
    mut v_stx_2375_: *mut leanh::LeanObject,
    mut v_a_2376_: *mut leanh::LeanObject,
    mut v_a_2377_: *mut leanh::LeanObject,
    mut v_a_2378_: *mut leanh::LeanObject,
    mut v_a_2379_: *mut leanh::LeanObject,
    mut v_a_2380_: *mut leanh::LeanObject,
    mut v_a_2381_: *mut leanh::LeanObject,
    mut v_a_2382_: *mut leanh::LeanObject,
    mut v_a_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: u8 = 0;
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__0;
    v___x_2386_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__1;
    v___x_2387_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1___closed__2;
    v___x_2388_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1;
    leanh::lean_inc(v_stx_2375_);
    v___x_2389_ = l_Lean_Syntax_isOfKind(v_stx_2375_, v___x_2388_);
    v___x_2390_ = 1;
    v___x_2391_ = leanh::lean_box((v___x_2389_) as usize);
    v___x_2392_ = leanh::lean_box((v___x_2390_) as usize);
    v___y_2393_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDSimpTrace___lam__0___boxed as *mut core::ffi::c_void,
        15,
        6,
    );
    leanh::lean_closure_set(v___y_2393_, 0, v___x_2391_);
    leanh::lean_closure_set(v___y_2393_, 1, v_stx_2375_);
    leanh::lean_closure_set(v___y_2393_, 2, v___x_2385_);
    leanh::lean_closure_set(v___y_2393_, 3, v___x_2386_);
    leanh::lean_closure_set(v___y_2393_, 4, v___x_2387_);
    leanh::lean_closure_set(v___y_2393_, 5, v___x_2392_);
    v___x_2394_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___y_2393_,
        v_a_2376_,
        v_a_2377_,
        v_a_2378_,
        v_a_2379_,
        v_a_2380_,
        v_a_2381_,
        v_a_2382_,
        v_a_2383_,
    );
    return v___x_2394_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed(
    mut v_stx_2395_: *mut leanh::LeanObject,
    mut v_a_2396_: *mut leanh::LeanObject,
    mut v_a_2397_: *mut leanh::LeanObject,
    mut v_a_2398_: *mut leanh::LeanObject,
    mut v_a_2399_: *mut leanh::LeanObject,
    mut v_a_2400_: *mut leanh::LeanObject,
    mut v_a_2401_: *mut leanh::LeanObject,
    mut v_a_2402_: *mut leanh::LeanObject,
    mut v_a_2403_: *mut leanh::LeanObject,
    mut v_a_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2405_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace(
        v_stx_2395_,
        v_a_2396_,
        v_a_2397_,
        v_a_2398_,
        v_a_2399_,
        v_a_2400_,
        v_a_2401_,
        v_a_2402_,
        v_a_2403_,
    );
    leanh::lean_dec(v_a_2403_);
    leanh::lean_dec_ref(v_a_2402_);
    leanh::lean_dec(v_a_2401_);
    leanh::lean_dec_ref(v_a_2400_);
    leanh::lean_dec(v_a_2399_);
    leanh::lean_dec_ref(v_a_2398_);
    leanh::lean_dec(v_a_2397_);
    leanh::lean_dec_ref(v_a_2396_);
    return v_res_2405_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1()
-> *mut leanh::LeanObject {
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2415_ = l_Lean_Elab_Tactic_Conv_evalDSimpTrace___closed__1;
    v___x_2416_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___closed__1;
    v___x_2417_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalDSimpTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2418_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2414_,
        v___x_2415_,
        v___x_2416_,
        v___x_2417_,
    );
    return v___x_2418_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1___boxed(
    mut v_a_2419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
    return v_res_2420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Simp(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalSimp_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpTrace__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalSimpMatch___regBuiltin_Lean_Elab_Tactic_Conv_evalSimpMatch_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimp___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimp_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Simp_0__Lean_Elab_Tactic_Conv_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_Conv_evalDSimpTrace__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Simp(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Simp(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_SimpTrace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
}