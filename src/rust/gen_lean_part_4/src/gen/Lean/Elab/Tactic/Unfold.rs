// Lean compiler output
// Module: Lean.Elab.Tactic.Unfold
// Imports: Lean.Meta.Tactic.Unfold Lean.Elab.Tactic.Location
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_st_ref_get, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_replaceRef};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
    l_Lean_Elab_Tactic_withoutRecover___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_elabTermForApply___boxed;
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    l_Lean_Elab_Tactic_withLocation, runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_FVarId_isLetVar___redArg;
use crate::r#gen::Lean::Meta::Tactic::Unfold::{
    initialize_Lean_Meta_Tactic_Unfold, l_Lean_Meta_unfoldLocalDecl, l_Lean_Meta_unfoldTarget,
    l_Lean_Meta_zetaDeltaLocalDecl, l_Lean_Meta_zetaDeltaTarget,
    runtime_initialize_Lean_Meta_Tactic_Unfold,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_throwTacticEx___redArg;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 102, 111, 108, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value) as *mut leanh::LeanObject,13034500471729497529 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 105, 100, 32, 110, 111, 116, 32, 117, 110, 102, 111, 108, 100, 32, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0_value: leanh::LeanStringObject<41> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [84, 97, 99, 116, 105, 99, 32, 96, 117, 110, 102, 111, 108, 100, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 76, 111, 99, 97, 108, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 104, 97, 115, 32, 110, 111, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 103, 108, 111, 98, 97, 108, 32, 111, 114, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18259345790759314728 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 85, 110, 102, 111, 108, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value) as *mut leanh::LeanObject,3655951909266319154 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [34, 117, 110, 102, 111, 108, 100, 32, 34, 32, 105, 100, 101, 110, 116, 43, 32, 40, 108, 111, 99, 97, 116, 105, 111, 110, 41, 63, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 129 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value) as *mut leanh::LeanObject,((( 44 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value) as *mut leanh::LeanObject,((( 129 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 58 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value) as *mut leanh::LeanObject,((( 48 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value) as *mut leanh::LeanObject,((( 58 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(
    mut v_declName_686_: *mut leanh::LeanObject,
    mut v_fvarId_687_: *mut leanh::LeanObject,
    mut v_a_688_: *mut leanh::LeanObject,
    mut v_a_689_: *mut leanh::LeanObject,
    mut v_a_690_: *mut leanh::LeanObject,
    mut v_a_691_: *mut leanh::LeanObject,
    mut v_a_692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_a_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_694_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_,
                );
                if leanh::lean_obj_tag(v___x_694_) == 0 {
                    v_a_695_ = leanh::lean_ctor_get(v___x_694_, 0);
                    leanh::lean_inc(v_a_695_);
                    leanh::lean_dec_ref_known(v___x_694_, 1);
                    v___x_696_ = l_Lean_Meta_unfoldLocalDecl(
                        v_a_695_,
                        v_fvarId_687_,
                        v_declName_686_,
                        v_a_689_,
                        v_a_690_,
                        v_a_691_,
                        v_a_692_,
                    );
                    if leanh::lean_obj_tag(v___x_696_) == 0 {
                        v_a_697_ = leanh::lean_ctor_get(v___x_696_, 0);
                        leanh::lean_inc(v_a_697_);
                        leanh::lean_dec_ref_known(v___x_696_, 1);
                        v___x_698_ = leanh::lean_box(0);
                        v___x_699_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_699_, 0, v_a_697_);
                        leanh::lean_ctor_set(v___x_699_, 1, v___x_698_);
                        v___x_700_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_699_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_,
                        );
                        return v___x_700_;
                    } else {
                        v_a_701_ = leanh::lean_ctor_get(v___x_696_, 0);
                        v_isSharedCheck_708_ = (!leanh::lean_is_exclusive(v___x_696_)) as u8;
                        if v_isSharedCheck_708_ == 0 {
                            v___x_703_ = v___x_696_;
                            v_isShared_704_ = v_isSharedCheck_708_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_701_);
                            leanh::lean_dec(v___x_696_);
                            v___x_703_ = leanh::lean_box(0);
                            v_isShared_704_ = v_isSharedCheck_708_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fvarId_687_);
                    leanh::lean_dec(v_declName_686_);
                    v_a_709_ = leanh::lean_ctor_get(v___x_694_, 0);
                    v_isSharedCheck_716_ = (!leanh::lean_is_exclusive(v___x_694_)) as u8;
                    if v_isSharedCheck_716_ == 0 {
                        v___x_711_ = v___x_694_;
                        v_isShared_712_ = v_isSharedCheck_716_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_709_);
                        leanh::lean_dec(v___x_694_);
                        v___x_711_ = leanh::lean_box(0);
                        v_isShared_712_ = v_isSharedCheck_716_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_704_ == 0 {
                    v___x_706_ = v___x_703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
                    v___x_706_ = v_reuseFailAlloc_707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_706_;
            }
            3 => {
                if v_isShared_712_ == 0 {
                    v___x_714_ = v___x_711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_715_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
                    v___x_714_ = v_reuseFailAlloc_715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldLocalDecl___redArg___boxed(
    mut v_declName_717_: *mut leanh::LeanObject,
    mut v_fvarId_718_: *mut leanh::LeanObject,
    mut v_a_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_a_721_: *mut leanh::LeanObject,
    mut v_a_722_: *mut leanh::LeanObject,
    mut v_a_723_: *mut leanh::LeanObject,
    mut v_a_724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_725_ = l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(
        v_declName_717_,
        v_fvarId_718_,
        v_a_719_,
        v_a_720_,
        v_a_721_,
        v_a_722_,
        v_a_723_,
    );
    leanh::lean_dec(v_a_723_);
    leanh::lean_dec_ref(v_a_722_);
    leanh::lean_dec(v_a_721_);
    leanh::lean_dec_ref(v_a_720_);
    leanh::lean_dec(v_a_719_);
    return v_res_725_;
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldLocalDecl(
    mut v_declName_726_: *mut leanh::LeanObject,
    mut v_fvarId_727_: *mut leanh::LeanObject,
    mut v_a_728_: *mut leanh::LeanObject,
    mut v_a_729_: *mut leanh::LeanObject,
    mut v_a_730_: *mut leanh::LeanObject,
    mut v_a_731_: *mut leanh::LeanObject,
    mut v_a_732_: *mut leanh::LeanObject,
    mut v_a_733_: *mut leanh::LeanObject,
    mut v_a_734_: *mut leanh::LeanObject,
    mut v_a_735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(
        v_declName_726_,
        v_fvarId_727_,
        v_a_729_,
        v_a_732_,
        v_a_733_,
        v_a_734_,
        v_a_735_,
    );
    return v___x_737_;
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldLocalDecl___boxed(
    mut v_declName_738_: *mut leanh::LeanObject,
    mut v_fvarId_739_: *mut leanh::LeanObject,
    mut v_a_740_: *mut leanh::LeanObject,
    mut v_a_741_: *mut leanh::LeanObject,
    mut v_a_742_: *mut leanh::LeanObject,
    mut v_a_743_: *mut leanh::LeanObject,
    mut v_a_744_: *mut leanh::LeanObject,
    mut v_a_745_: *mut leanh::LeanObject,
    mut v_a_746_: *mut leanh::LeanObject,
    mut v_a_747_: *mut leanh::LeanObject,
    mut v_a_748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_749_ = l_Lean_Elab_Tactic_unfoldLocalDecl(
        v_declName_738_,
        v_fvarId_739_,
        v_a_740_,
        v_a_741_,
        v_a_742_,
        v_a_743_,
        v_a_744_,
        v_a_745_,
        v_a_746_,
        v_a_747_,
    );
    leanh::lean_dec(v_a_747_);
    leanh::lean_dec_ref(v_a_746_);
    leanh::lean_dec(v_a_745_);
    leanh::lean_dec_ref(v_a_744_);
    leanh::lean_dec(v_a_743_);
    leanh::lean_dec_ref(v_a_742_);
    leanh::lean_dec(v_a_741_);
    leanh::lean_dec_ref(v_a_740_);
    return v_res_749_;
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldTarget___redArg(
    mut v_declName_750_: *mut leanh::LeanObject,
    mut v_a_751_: *mut leanh::LeanObject,
    mut v_a_752_: *mut leanh::LeanObject,
    mut v_a_753_: *mut leanh::LeanObject,
    mut v_a_754_: *mut leanh::LeanObject,
    mut v_a_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_767_: u8 = 0;
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_771_: u8 = 0;
    let mut v_a_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_775_: u8 = 0;
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_757_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_,
                );
                if leanh::lean_obj_tag(v___x_757_) == 0 {
                    v_a_758_ = leanh::lean_ctor_get(v___x_757_, 0);
                    leanh::lean_inc(v_a_758_);
                    leanh::lean_dec_ref_known(v___x_757_, 1);
                    v___x_759_ = l_Lean_Meta_unfoldTarget(
                        v_a_758_,
                        v_declName_750_,
                        v_a_752_,
                        v_a_753_,
                        v_a_754_,
                        v_a_755_,
                    );
                    if leanh::lean_obj_tag(v___x_759_) == 0 {
                        v_a_760_ = leanh::lean_ctor_get(v___x_759_, 0);
                        leanh::lean_inc(v_a_760_);
                        leanh::lean_dec_ref_known(v___x_759_, 1);
                        v___x_761_ = leanh::lean_box(0);
                        v___x_762_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_762_, 0, v_a_760_);
                        leanh::lean_ctor_set(v___x_762_, 1, v___x_761_);
                        v___x_763_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_762_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_,
                        );
                        return v___x_763_;
                    } else {
                        v_a_764_ = leanh::lean_ctor_get(v___x_759_, 0);
                        v_isSharedCheck_771_ = (!leanh::lean_is_exclusive(v___x_759_)) as u8;
                        if v_isSharedCheck_771_ == 0 {
                            v___x_766_ = v___x_759_;
                            v_isShared_767_ = v_isSharedCheck_771_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_764_);
                            leanh::lean_dec(v___x_759_);
                            v___x_766_ = leanh::lean_box(0);
                            v_isShared_767_ = v_isSharedCheck_771_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_750_);
                    v_a_772_ = leanh::lean_ctor_get(v___x_757_, 0);
                    v_isSharedCheck_779_ = (!leanh::lean_is_exclusive(v___x_757_)) as u8;
                    if v_isSharedCheck_779_ == 0 {
                        v___x_774_ = v___x_757_;
                        v_isShared_775_ = v_isSharedCheck_779_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_772_);
                        leanh::lean_dec(v___x_757_);
                        v___x_774_ = leanh::lean_box(0);
                        v_isShared_775_ = v_isSharedCheck_779_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_767_ == 0 {
                    v___x_769_ = v___x_766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
                    v___x_769_ = v_reuseFailAlloc_770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_769_;
            }
            3 => {
                if v_isShared_775_ == 0 {
                    v___x_777_ = v___x_774_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_778_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
                    v___x_777_ = v_reuseFailAlloc_778_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldTarget___redArg___boxed(
    mut v_declName_780_: *mut leanh::LeanObject,
    mut v_a_781_: *mut leanh::LeanObject,
    mut v_a_782_: *mut leanh::LeanObject,
    mut v_a_783_: *mut leanh::LeanObject,
    mut v_a_784_: *mut leanh::LeanObject,
    mut v_a_785_: *mut leanh::LeanObject,
    mut v_a_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lean_Elab_Tactic_unfoldTarget___redArg(
        v_declName_780_,
        v_a_781_,
        v_a_782_,
        v_a_783_,
        v_a_784_,
        v_a_785_,
    );
    leanh::lean_dec(v_a_785_);
    leanh::lean_dec_ref(v_a_784_);
    leanh::lean_dec(v_a_783_);
    leanh::lean_dec_ref(v_a_782_);
    leanh::lean_dec(v_a_781_);
    return v_res_787_;
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldTarget(
    mut v_declName_788_: *mut leanh::LeanObject,
    mut v_a_789_: *mut leanh::LeanObject,
    mut v_a_790_: *mut leanh::LeanObject,
    mut v_a_791_: *mut leanh::LeanObject,
    mut v_a_792_: *mut leanh::LeanObject,
    mut v_a_793_: *mut leanh::LeanObject,
    mut v_a_794_: *mut leanh::LeanObject,
    mut v_a_795_: *mut leanh::LeanObject,
    mut v_a_796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_Elab_Tactic_unfoldTarget___redArg(
        v_declName_788_,
        v_a_790_,
        v_a_793_,
        v_a_794_,
        v_a_795_,
        v_a_796_,
    );
    return v___x_798_;
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldTarget___boxed(
    mut v_declName_799_: *mut leanh::LeanObject,
    mut v_a_800_: *mut leanh::LeanObject,
    mut v_a_801_: *mut leanh::LeanObject,
    mut v_a_802_: *mut leanh::LeanObject,
    mut v_a_803_: *mut leanh::LeanObject,
    mut v_a_804_: *mut leanh::LeanObject,
    mut v_a_805_: *mut leanh::LeanObject,
    mut v_a_806_: *mut leanh::LeanObject,
    mut v_a_807_: *mut leanh::LeanObject,
    mut v_a_808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Lean_Elab_Tactic_unfoldTarget(
        v_declName_799_,
        v_a_800_,
        v_a_801_,
        v_a_802_,
        v_a_803_,
        v_a_804_,
        v_a_805_,
        v_a_806_,
        v_a_807_,
    );
    leanh::lean_dec(v_a_807_);
    leanh::lean_dec_ref(v_a_806_);
    leanh::lean_dec(v_a_805_);
    leanh::lean_dec_ref(v_a_804_);
    leanh::lean_dec(v_a_803_);
    leanh::lean_dec_ref(v_a_802_);
    leanh::lean_dec(v_a_801_);
    leanh::lean_dec_ref(v_a_800_);
    return v_res_809_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(
    mut v_declFVarId_810_: *mut leanh::LeanObject,
    mut v_fvarId_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
    mut v_a_814_: *mut leanh::LeanObject,
    mut v_a_815_: *mut leanh::LeanObject,
    mut v_a_816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_828_: u8 = 0;
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut v_a_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_818_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_,
                );
                if leanh::lean_obj_tag(v___x_818_) == 0 {
                    v_a_819_ = leanh::lean_ctor_get(v___x_818_, 0);
                    leanh::lean_inc(v_a_819_);
                    leanh::lean_dec_ref_known(v___x_818_, 1);
                    v___x_820_ = l_Lean_Meta_zetaDeltaLocalDecl(
                        v_a_819_,
                        v_fvarId_811_,
                        v_declFVarId_810_,
                        v_a_813_,
                        v_a_814_,
                        v_a_815_,
                        v_a_816_,
                    );
                    if leanh::lean_obj_tag(v___x_820_) == 0 {
                        v_a_821_ = leanh::lean_ctor_get(v___x_820_, 0);
                        leanh::lean_inc(v_a_821_);
                        leanh::lean_dec_ref_known(v___x_820_, 1);
                        v___x_822_ = leanh::lean_box(0);
                        v___x_823_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_823_, 0, v_a_821_);
                        leanh::lean_ctor_set(v___x_823_, 1, v___x_822_);
                        v___x_824_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_823_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_,
                        );
                        return v___x_824_;
                    } else {
                        v_a_825_ = leanh::lean_ctor_get(v___x_820_, 0);
                        v_isSharedCheck_832_ = (!leanh::lean_is_exclusive(v___x_820_)) as u8;
                        if v_isSharedCheck_832_ == 0 {
                            v___x_827_ = v___x_820_;
                            v_isShared_828_ = v_isSharedCheck_832_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_825_);
                            leanh::lean_dec(v___x_820_);
                            v___x_827_ = leanh::lean_box(0);
                            v_isShared_828_ = v_isSharedCheck_832_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fvarId_811_);
                    leanh::lean_dec(v_declFVarId_810_);
                    v_a_833_ = leanh::lean_ctor_get(v___x_818_, 0);
                    v_isSharedCheck_840_ = (!leanh::lean_is_exclusive(v___x_818_)) as u8;
                    if v_isSharedCheck_840_ == 0 {
                        v___x_835_ = v___x_818_;
                        v_isShared_836_ = v_isSharedCheck_840_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_833_);
                        leanh::lean_dec(v___x_818_);
                        v___x_835_ = leanh::lean_box(0);
                        v_isShared_836_ = v_isSharedCheck_840_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_828_ == 0 {
                    v___x_830_ = v___x_827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
                    v___x_830_ = v_reuseFailAlloc_831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_830_;
            }
            3 => {
                if v_isShared_836_ == 0 {
                    v___x_838_ = v___x_835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
                    v___x_838_ = v_reuseFailAlloc_839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg___boxed(
    mut v_declFVarId_841_: *mut leanh::LeanObject,
    mut v_fvarId_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
    mut v_a_844_: *mut leanh::LeanObject,
    mut v_a_845_: *mut leanh::LeanObject,
    mut v_a_846_: *mut leanh::LeanObject,
    mut v_a_847_: *mut leanh::LeanObject,
    mut v_a_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_849_ = l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(
        v_declFVarId_841_,
        v_fvarId_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
        v_a_847_,
    );
    leanh::lean_dec(v_a_847_);
    leanh::lean_dec_ref(v_a_846_);
    leanh::lean_dec(v_a_845_);
    leanh::lean_dec_ref(v_a_844_);
    leanh::lean_dec(v_a_843_);
    return v_res_849_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaLocalDecl(
    mut v_declFVarId_850_: *mut leanh::LeanObject,
    mut v_fvarId_851_: *mut leanh::LeanObject,
    mut v_a_852_: *mut leanh::LeanObject,
    mut v_a_853_: *mut leanh::LeanObject,
    mut v_a_854_: *mut leanh::LeanObject,
    mut v_a_855_: *mut leanh::LeanObject,
    mut v_a_856_: *mut leanh::LeanObject,
    mut v_a_857_: *mut leanh::LeanObject,
    mut v_a_858_: *mut leanh::LeanObject,
    mut v_a_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_861_ = l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(
        v_declFVarId_850_,
        v_fvarId_851_,
        v_a_853_,
        v_a_856_,
        v_a_857_,
        v_a_858_,
        v_a_859_,
    );
    return v___x_861_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaLocalDecl___boxed(
    mut v_declFVarId_862_: *mut leanh::LeanObject,
    mut v_fvarId_863_: *mut leanh::LeanObject,
    mut v_a_864_: *mut leanh::LeanObject,
    mut v_a_865_: *mut leanh::LeanObject,
    mut v_a_866_: *mut leanh::LeanObject,
    mut v_a_867_: *mut leanh::LeanObject,
    mut v_a_868_: *mut leanh::LeanObject,
    mut v_a_869_: *mut leanh::LeanObject,
    mut v_a_870_: *mut leanh::LeanObject,
    mut v_a_871_: *mut leanh::LeanObject,
    mut v_a_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ = l_Lean_Elab_Tactic_zetaDeltaLocalDecl(
        v_declFVarId_862_,
        v_fvarId_863_,
        v_a_864_,
        v_a_865_,
        v_a_866_,
        v_a_867_,
        v_a_868_,
        v_a_869_,
        v_a_870_,
        v_a_871_,
    );
    leanh::lean_dec(v_a_871_);
    leanh::lean_dec_ref(v_a_870_);
    leanh::lean_dec(v_a_869_);
    leanh::lean_dec_ref(v_a_868_);
    leanh::lean_dec(v_a_867_);
    leanh::lean_dec_ref(v_a_866_);
    leanh::lean_dec(v_a_865_);
    leanh::lean_dec_ref(v_a_864_);
    return v_res_873_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(
    mut v_declFVarId_874_: *mut leanh::LeanObject,
    mut v_a_875_: *mut leanh::LeanObject,
    mut v_a_876_: *mut leanh::LeanObject,
    mut v_a_877_: *mut leanh::LeanObject,
    mut v_a_878_: *mut leanh::LeanObject,
    mut v_a_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v_a_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_881_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_,
                );
                if leanh::lean_obj_tag(v___x_881_) == 0 {
                    v_a_882_ = leanh::lean_ctor_get(v___x_881_, 0);
                    leanh::lean_inc(v_a_882_);
                    leanh::lean_dec_ref_known(v___x_881_, 1);
                    v___x_883_ = l_Lean_Meta_zetaDeltaTarget(
                        v_a_882_,
                        v_declFVarId_874_,
                        v_a_876_,
                        v_a_877_,
                        v_a_878_,
                        v_a_879_,
                    );
                    if leanh::lean_obj_tag(v___x_883_) == 0 {
                        v_a_884_ = leanh::lean_ctor_get(v___x_883_, 0);
                        leanh::lean_inc(v_a_884_);
                        leanh::lean_dec_ref_known(v___x_883_, 1);
                        v___x_885_ = leanh::lean_box(0);
                        v___x_886_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_886_, 0, v_a_884_);
                        leanh::lean_ctor_set(v___x_886_, 1, v___x_885_);
                        v___x_887_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_886_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_,
                        );
                        return v___x_887_;
                    } else {
                        v_a_888_ = leanh::lean_ctor_get(v___x_883_, 0);
                        v_isSharedCheck_895_ = (!leanh::lean_is_exclusive(v___x_883_)) as u8;
                        if v_isSharedCheck_895_ == 0 {
                            v___x_890_ = v___x_883_;
                            v_isShared_891_ = v_isSharedCheck_895_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_888_);
                            leanh::lean_dec(v___x_883_);
                            v___x_890_ = leanh::lean_box(0);
                            v_isShared_891_ = v_isSharedCheck_895_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declFVarId_874_);
                    v_a_896_ = leanh::lean_ctor_get(v___x_881_, 0);
                    v_isSharedCheck_903_ = (!leanh::lean_is_exclusive(v___x_881_)) as u8;
                    if v_isSharedCheck_903_ == 0 {
                        v___x_898_ = v___x_881_;
                        v_isShared_899_ = v_isSharedCheck_903_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_896_);
                        leanh::lean_dec(v___x_881_);
                        v___x_898_ = leanh::lean_box(0);
                        v_isShared_899_ = v_isSharedCheck_903_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_891_ == 0 {
                    v___x_893_ = v___x_890_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
                    v___x_893_ = v_reuseFailAlloc_894_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_893_;
            }
            3 => {
                if v_isShared_899_ == 0 {
                    v___x_901_ = v___x_898_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_902_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
                    v___x_901_ = v_reuseFailAlloc_902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaTarget___redArg___boxed(
    mut v_declFVarId_904_: *mut leanh::LeanObject,
    mut v_a_905_: *mut leanh::LeanObject,
    mut v_a_906_: *mut leanh::LeanObject,
    mut v_a_907_: *mut leanh::LeanObject,
    mut v_a_908_: *mut leanh::LeanObject,
    mut v_a_909_: *mut leanh::LeanObject,
    mut v_a_910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_911_ = l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(
        v_declFVarId_904_,
        v_a_905_,
        v_a_906_,
        v_a_907_,
        v_a_908_,
        v_a_909_,
    );
    leanh::lean_dec(v_a_909_);
    leanh::lean_dec_ref(v_a_908_);
    leanh::lean_dec(v_a_907_);
    leanh::lean_dec_ref(v_a_906_);
    leanh::lean_dec(v_a_905_);
    return v_res_911_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaTarget(
    mut v_declFVarId_912_: *mut leanh::LeanObject,
    mut v_a_913_: *mut leanh::LeanObject,
    mut v_a_914_: *mut leanh::LeanObject,
    mut v_a_915_: *mut leanh::LeanObject,
    mut v_a_916_: *mut leanh::LeanObject,
    mut v_a_917_: *mut leanh::LeanObject,
    mut v_a_918_: *mut leanh::LeanObject,
    mut v_a_919_: *mut leanh::LeanObject,
    mut v_a_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_922_ = l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(
        v_declFVarId_912_,
        v_a_914_,
        v_a_917_,
        v_a_918_,
        v_a_919_,
        v_a_920_,
    );
    return v___x_922_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaTarget___boxed(
    mut v_declFVarId_923_: *mut leanh::LeanObject,
    mut v_a_924_: *mut leanh::LeanObject,
    mut v_a_925_: *mut leanh::LeanObject,
    mut v_a_926_: *mut leanh::LeanObject,
    mut v_a_927_: *mut leanh::LeanObject,
    mut v_a_928_: *mut leanh::LeanObject,
    mut v_a_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_a_931_: *mut leanh::LeanObject,
    mut v_a_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_933_ = l_Lean_Elab_Tactic_zetaDeltaTarget(
        v_declFVarId_923_,
        v_a_924_,
        v_a_925_,
        v_a_926_,
        v_a_927_,
        v_a_928_,
        v_a_929_,
        v_a_930_,
        v_a_931_,
    );
    leanh::lean_dec(v_a_931_);
    leanh::lean_dec_ref(v_a_930_);
    leanh::lean_dec(v_a_929_);
    leanh::lean_dec_ref(v_a_928_);
    leanh::lean_dec(v_a_927_);
    leanh::lean_dec_ref(v_a_926_);
    leanh::lean_dec(v_a_925_);
    leanh::lean_dec_ref(v_a_924_);
    return v_res_933_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2;
    v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
    return v___x_939_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_941_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4;
    v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
    return v___x_942_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0(
    mut v_declName_943_: *mut leanh::LeanObject,
    mut v_x_944_: *mut leanh::LeanObject,
    mut v___y_945_: *mut leanh::LeanObject,
    mut v___y_946_: *mut leanh::LeanObject,
    mut v___y_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
    mut v___y_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
    mut v___y_951_: *mut leanh::LeanObject,
    mut v___y_952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_954_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1;
    v___x_955_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3);
    v___x_956_ = l_Lean_MessageData_ofName(v_declName_943_);
    v___x_957_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_957_, 0, v___x_955_);
    leanh::lean_ctor_set(v___x_957_, 1, v___x_956_);
    v___x_958_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5);
    v___x_959_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_959_, 0, v___x_957_);
    leanh::lean_ctor_set(v___x_959_, 1, v___x_958_);
    v___x_960_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_960_, 0, v___x_959_);
    v___x_961_ = l_Lean_Meta_throwTacticEx___redArg(
        v___x_954_, v_x_944_, v___x_960_, v___y_949_, v___y_950_, v___y_951_, v___y_952_,
    );
    return v___x_961_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___boxed(
    mut v_declName_962_: *mut leanh::LeanObject,
    mut v_x_963_: *mut leanh::LeanObject,
    mut v___y_964_: *mut leanh::LeanObject,
    mut v___y_965_: *mut leanh::LeanObject,
    mut v___y_966_: *mut leanh::LeanObject,
    mut v___y_967_: *mut leanh::LeanObject,
    mut v___y_968_: *mut leanh::LeanObject,
    mut v___y_969_: *mut leanh::LeanObject,
    mut v___y_970_: *mut leanh::LeanObject,
    mut v___y_971_: *mut leanh::LeanObject,
    mut v___y_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_973_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0(
        v_declName_962_,
        v_x_963_,
        v___y_964_,
        v___y_965_,
        v___y_966_,
        v___y_967_,
        v___y_968_,
        v___y_969_,
        v___y_970_,
        v___y_971_,
    );
    leanh::lean_dec(v___y_971_);
    leanh::lean_dec_ref(v___y_970_);
    leanh::lean_dec(v___y_969_);
    leanh::lean_dec_ref(v___y_968_);
    leanh::lean_dec(v___y_967_);
    leanh::lean_dec_ref(v___y_966_);
    leanh::lean_dec(v___y_965_);
    leanh::lean_dec_ref(v___y_964_);
    return v_res_973_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1(
    mut v_a_974_: *mut leanh::LeanObject,
    mut v_x_975_: *mut leanh::LeanObject,
    mut v___y_976_: *mut leanh::LeanObject,
    mut v___y_977_: *mut leanh::LeanObject,
    mut v___y_978_: *mut leanh::LeanObject,
    mut v___y_979_: *mut leanh::LeanObject,
    mut v___y_980_: *mut leanh::LeanObject,
    mut v___y_981_: *mut leanh::LeanObject,
    mut v___y_982_: *mut leanh::LeanObject,
    mut v___y_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1;
    v___x_986_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3);
    v___x_987_ = l_Lean_MessageData_ofExpr(v_a_974_);
    v___x_988_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_988_, 0, v___x_986_);
    leanh::lean_ctor_set(v___x_988_, 1, v___x_987_);
    v___x_989_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5);
    v___x_990_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_990_, 0, v___x_988_);
    leanh::lean_ctor_set(v___x_990_, 1, v___x_989_);
    v___x_991_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_991_, 0, v___x_990_);
    v___x_992_ = l_Lean_Meta_throwTacticEx___redArg(
        v___x_985_, v_x_975_, v___x_991_, v___y_980_, v___y_981_, v___y_982_, v___y_983_,
    );
    return v___x_992_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1___boxed(
    mut v_a_993_: *mut leanh::LeanObject,
    mut v_x_994_: *mut leanh::LeanObject,
    mut v___y_995_: *mut leanh::LeanObject,
    mut v___y_996_: *mut leanh::LeanObject,
    mut v___y_997_: *mut leanh::LeanObject,
    mut v___y_998_: *mut leanh::LeanObject,
    mut v___y_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
    mut v___y_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1004_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1(
        v_a_993_,
        v_x_994_,
        v___y_995_,
        v___y_996_,
        v___y_997_,
        v___y_998_,
        v___y_999_,
        v___y_1000_,
        v___y_1001_,
        v___y_1002_,
    );
    leanh::lean_dec(v___y_1002_);
    leanh::lean_dec_ref(v___y_1001_);
    leanh::lean_dec(v___y_1000_);
    leanh::lean_dec_ref(v___y_999_);
    leanh::lean_dec(v___y_998_);
    leanh::lean_dec_ref(v___y_997_);
    leanh::lean_dec(v___y_996_);
    leanh::lean_dec_ref(v___y_995_);
    return v_res_1004_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(
    mut v_msgData_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = lean_st_ref_get(v___y_1009_);
    v_env_1012_ = leanh::lean_ctor_get(v___x_1011_, 0);
    leanh::lean_inc_ref(v_env_1012_);
    leanh::lean_dec(v___x_1011_);
    v___x_1013_ = lean_st_ref_get(v___y_1007_);
    v_mctx_1014_ = leanh::lean_ctor_get(v___x_1013_, 0);
    leanh::lean_inc_ref(v_mctx_1014_);
    leanh::lean_dec(v___x_1013_);
    v_lctx_1015_ = leanh::lean_ctor_get(v___y_1006_, 2);
    v_options_1016_ = leanh::lean_ctor_get(v___y_1008_, 2);
    leanh::lean_inc_ref(v_options_1016_);
    leanh::lean_inc_ref(v_lctx_1015_);
    v___x_1017_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1017_, 0, v_env_1012_);
    leanh::lean_ctor_set(v___x_1017_, 1, v_mctx_1014_);
    leanh::lean_ctor_set(v___x_1017_, 2, v_lctx_1015_);
    leanh::lean_ctor_set(v___x_1017_, 3, v_options_1016_);
    v___x_1018_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1018_, 0, v___x_1017_);
    leanh::lean_ctor_set(v___x_1018_, 1, v_msgData_1005_);
    v___x_1019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    return v___x_1019_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0___boxed(
    mut v_msgData_1020_: *mut leanh::LeanObject,
    mut v___y_1021_: *mut leanh::LeanObject,
    mut v___y_1022_: *mut leanh::LeanObject,
    mut v___y_1023_: *mut leanh::LeanObject,
    mut v___y_1024_: *mut leanh::LeanObject,
    mut v___y_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(v_msgData_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
    leanh::lean_dec(v___y_1024_);
    leanh::lean_dec_ref(v___y_1023_);
    leanh::lean_dec(v___y_1022_);
    leanh::lean_dec_ref(v___y_1021_);
    return v_res_1026_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(
    mut v_msg_1027_: *mut leanh::LeanObject,
    mut v___y_1028_: *mut leanh::LeanObject,
    mut v___y_1029_: *mut leanh::LeanObject,
    mut v___y_1030_: *mut leanh::LeanObject,
    mut v___y_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1033_ = leanh::lean_ctor_get(v___y_1030_, 5);
                v___x_1034_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(v_msg_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
                v_a_1035_ = leanh::lean_ctor_get(v___x_1034_, 0);
                v_isSharedCheck_1043_ = (!leanh::lean_is_exclusive(v___x_1034_)) as u8;
                if v_isSharedCheck_1043_ == 0 {
                    v___x_1037_ = v___x_1034_;
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1035_);
                    leanh::lean_dec(v___x_1034_);
                    v___x_1037_ = leanh::lean_box(0);
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1033_);
                v___x_1039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1039_, 0, v_ref_1033_);
                leanh::lean_ctor_set(v___x_1039_, 1, v_a_1035_);
                if v_isShared_1038_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1037_, 1);
                    leanh::lean_ctor_set(v___x_1037_, 0, v___x_1039_);
                    v___x_1041_ = v___x_1037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
                    v___x_1041_ = v_reuseFailAlloc_1042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg___boxed(
    mut v_msg_1044_: *mut leanh::LeanObject,
    mut v___y_1045_: *mut leanh::LeanObject,
    mut v___y_1046_: *mut leanh::LeanObject,
    mut v___y_1047_: *mut leanh::LeanObject,
    mut v___y_1048_: *mut leanh::LeanObject,
    mut v___y_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v_msg_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
    leanh::lean_dec(v___y_1048_);
    leanh::lean_dec_ref(v___y_1047_);
    leanh::lean_dec(v___y_1046_);
    leanh::lean_dec_ref(v___y_1045_);
    return v_res_1050_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0;
    v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
    return v___x_1053_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2;
    v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
    return v___x_1056_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4;
    v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
    return v___x_1059_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1061_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6;
    v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
    return v___x_1062_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2(
    mut v_declNameId_1063_: *mut leanh::LeanObject,
    mut v___x_1064_: *mut leanh::LeanObject,
    mut v_loc_1065_: *mut leanh::LeanObject,
    mut v___x_1066_: u8,
    mut v___y_1067_: *mut leanh::LeanObject,
    mut v___y_1068_: *mut leanh::LeanObject,
    mut v___y_1069_: *mut leanh::LeanObject,
    mut v___y_1070_: *mut leanh::LeanObject,
    mut v___y_1071_: *mut leanh::LeanObject,
    mut v___y_1072_: *mut leanh::LeanObject,
    mut v___y_1073_: *mut leanh::LeanObject,
    mut v___y_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1088_: u8 = 0;
    let mut v_cancelTk_x3f_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1090_: u8 = 0;
    let mut v_inheritedTraceOptions_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v_ref_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: u8 = 0;
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1131_: u8 = 0;
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1135_: u8 = 0;
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1149_: u8 = 0;
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1153_: u8 = 0;
    let mut v_a_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1161_: u8 = 0;
    let mut v_reuseFailAlloc_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1076_ = leanh::lean_ctor_get(v___y_1073_, 0);
                v_fileMap_1077_ = leanh::lean_ctor_get(v___y_1073_, 1);
                v_options_1078_ = leanh::lean_ctor_get(v___y_1073_, 2);
                v_currRecDepth_1079_ = leanh::lean_ctor_get(v___y_1073_, 3);
                v_maxRecDepth_1080_ = leanh::lean_ctor_get(v___y_1073_, 4);
                v_ref_1081_ = leanh::lean_ctor_get(v___y_1073_, 5);
                v_currNamespace_1082_ = leanh::lean_ctor_get(v___y_1073_, 6);
                v_openDecls_1083_ = leanh::lean_ctor_get(v___y_1073_, 7);
                v_initHeartbeats_1084_ = leanh::lean_ctor_get(v___y_1073_, 8);
                v_maxHeartbeats_1085_ = leanh::lean_ctor_get(v___y_1073_, 9);
                v_quotContext_1086_ = leanh::lean_ctor_get(v___y_1073_, 10);
                v_currMacroScope_1087_ = leanh::lean_ctor_get(v___y_1073_, 11);
                v_diag_1088_ = leanh::lean_ctor_get_uint8(
                    v___y_1073_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1089_ = leanh::lean_ctor_get(v___y_1073_, 12);
                v_suppressElabErrors_1090_ = leanh::lean_ctor_get_uint8(
                    v___y_1073_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1091_ = leanh::lean_ctor_get(v___y_1073_, 13);
                v_isSharedCheck_1163_ = (!leanh::lean_is_exclusive(v___y_1073_)) as u8;
                if v_isSharedCheck_1163_ == 0 {
                    v___x_1093_ = v___y_1073_;
                    v_isShared_1094_ = v_isSharedCheck_1163_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_1091_);
                    leanh::lean_inc(v_cancelTk_x3f_1089_);
                    leanh::lean_inc(v_currMacroScope_1087_);
                    leanh::lean_inc(v_quotContext_1086_);
                    leanh::lean_inc(v_maxHeartbeats_1085_);
                    leanh::lean_inc(v_initHeartbeats_1084_);
                    leanh::lean_inc(v_openDecls_1083_);
                    leanh::lean_inc(v_currNamespace_1082_);
                    leanh::lean_inc(v_ref_1081_);
                    leanh::lean_inc(v_maxRecDepth_1080_);
                    leanh::lean_inc(v_currRecDepth_1079_);
                    leanh::lean_inc(v_options_1078_);
                    leanh::lean_inc(v_fileMap_1077_);
                    leanh::lean_inc(v_fileName_1076_);
                    leanh::lean_dec(v___y_1073_);
                    v___x_1093_ = leanh::lean_box(0);
                    v_isShared_1094_ = v_isSharedCheck_1163_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_1095_ = l_Lean_replaceRef(v_declNameId_1063_, v_ref_1081_);
                leanh::lean_dec(v_ref_1081_);
                if v_isShared_1094_ == 0 {
                    leanh::lean_ctor_set(v___x_1093_, 5, v_ref_1095_);
                    v___x_1097_ = v___x_1093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_fileName_1076_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_fileMap_1077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_options_1078_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_currRecDepth_1079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_maxRecDepth_1080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_ref_1095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_currNamespace_1082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 7, v_openDecls_1083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_initHeartbeats_1084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 9, v_maxHeartbeats_1085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 10, v_quotContext_1086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 11, v_currMacroScope_1087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 12, v_cancelTk_x3f_1089_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1162_,
                        13,
                        v_inheritedTraceOptions_1091_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1162_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_1088_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1162_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_1090_,
                    );
                    v___x_1097_ = v_reuseFailAlloc_1162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1098_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                    v___x_1064_,
                    v___y_1067_,
                    v___y_1068_,
                    v___y_1069_,
                    v___y_1070_,
                    v___y_1071_,
                    v___y_1072_,
                    v___x_1097_,
                    v___y_1074_,
                );
                if leanh::lean_obj_tag(v___x_1098_) == 0 {
                    v_a_1099_ = leanh::lean_ctor_get(v___x_1098_, 0);
                    leanh::lean_inc(v_a_1099_);
                    leanh::lean_dec_ref_known(v___x_1098_, 1);
                    match leanh::lean_obj_tag(v_a_1099_) {
                        4 => {
                            v_declName_1100_ = leanh::lean_ctor_get(v_a_1099_, 0);
                            leanh::lean_inc_n(v_declName_1100_, 3);
                            leanh::lean_dec_ref_known(v_a_1099_, 2);
                            v___f_1101_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                            leanh::lean_closure_set(v___f_1101_, 0, v_declName_1100_);
                            v___x_1102_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_unfoldLocalDecl___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                1,
                            );
                            leanh::lean_closure_set(v___x_1102_, 0, v_declName_1100_);
                            v___x_1103_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_unfoldTarget___boxed as *mut core::ffi::c_void,
                                10,
                                1,
                            );
                            leanh::lean_closure_set(v___x_1103_, 0, v_declName_1100_);
                            v___x_1104_ = l_Lean_Elab_Tactic_withLocation(
                                v_loc_1065_,
                                v___x_1102_,
                                v___x_1103_,
                                v___f_1101_,
                                v___y_1067_,
                                v___y_1068_,
                                v___y_1069_,
                                v___y_1070_,
                                v___y_1071_,
                                v___y_1072_,
                                v___x_1097_,
                                v___y_1074_,
                            );
                            leanh::lean_dec_ref(v___x_1097_);
                            return v___x_1104_;
                        }
                        1 => {
                            v_fvarId_1105_ = leanh::lean_ctor_get(v_a_1099_, 0);
                            leanh::lean_inc(v_fvarId_1105_);
                            v___x_1106_ = l_Lean_FVarId_isLetVar___redArg(
                                v_fvarId_1105_,
                                v___x_1066_,
                                v___y_1071_,
                                v___x_1097_,
                                v___y_1074_,
                            );
                            if leanh::lean_obj_tag(v___x_1106_) == 0 {
                                v_a_1107_ = leanh::lean_ctor_get(v___x_1106_, 0);
                                leanh::lean_inc(v_a_1107_);
                                leanh::lean_dec_ref_known(v___x_1106_, 1);
                                leanh::lean_inc_ref(v_a_1099_);
                                v___f_1108_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1___boxed as *mut core::ffi::c_void, 11, 1);
                                leanh::lean_closure_set(v___f_1108_, 0, v_a_1099_);
                                v___x_1121_ = (leanh::lean_unbox(v_a_1107_) as u8);
                                leanh::lean_dec(v_a_1107_);
                                if v___x_1121_ == 0 {
                                    leanh::lean_dec_ref(v___f_1108_);
                                    v___x_1122_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1);
                                    v___x_1123_ = l_Lean_MessageData_ofExpr(v_a_1099_);
                                    v___x_1124_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1124_, 0, v___x_1122_);
                                    leanh::lean_ctor_set(v___x_1124_, 1, v___x_1123_);
                                    v___x_1125_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3);
                                    v___x_1126_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1126_, 0, v___x_1124_);
                                    leanh::lean_ctor_set(v___x_1126_, 1, v___x_1125_);
                                    v___x_1127_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v___x_1126_, v___y_1071_, v___y_1072_, v___x_1097_, v___y_1074_);
                                    leanh::lean_dec_ref(v___x_1097_);
                                    return v___x_1127_;
                                } else {
                                    leanh::lean_inc(v_fvarId_1105_);
                                    leanh::lean_dec_ref_known(v_a_1099_, 1);
                                    v___y_1110_ = v___y_1067_;
                                    v___y_1111_ = v___y_1068_;
                                    v___y_1112_ = v___y_1069_;
                                    v___y_1113_ = v___y_1070_;
                                    v___y_1114_ = v___y_1071_;
                                    v___y_1115_ = v___y_1072_;
                                    v___y_1116_ = v___x_1097_;
                                    v___y_1117_ = v___y_1074_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_a_1099_, 1);
                                leanh::lean_dec_ref(v___x_1097_);
                                v_a_1128_ = leanh::lean_ctor_get(v___x_1106_, 0);
                                v_isSharedCheck_1135_ =
                                    (!leanh::lean_is_exclusive(v___x_1106_)) as u8;
                                if v_isSharedCheck_1135_ == 0 {
                                    v___x_1130_ = v___x_1106_;
                                    v_isShared_1131_ = v_isSharedCheck_1135_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1128_);
                                    leanh::lean_dec(v___x_1106_);
                                    v___x_1130_ = leanh::lean_box(0);
                                    v_isShared_1131_ = v_isSharedCheck_1135_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v___x_1136_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v___y_1068_,
                                v___y_1071_,
                                v___y_1072_,
                                v___x_1097_,
                                v___y_1074_,
                            );
                            if leanh::lean_obj_tag(v___x_1136_) == 0 {
                                v_a_1137_ = leanh::lean_ctor_get(v___x_1136_, 0);
                                leanh::lean_inc(v_a_1137_);
                                leanh::lean_dec_ref_known(v___x_1136_, 1);
                                v___x_1138_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1;
                                v___x_1139_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5);
                                v___x_1140_ = l_Lean_MessageData_ofExpr(v_a_1099_);
                                v___x_1141_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1141_, 0, v___x_1139_);
                                leanh::lean_ctor_set(v___x_1141_, 1, v___x_1140_);
                                v___x_1142_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7);
                                v___x_1143_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1143_, 0, v___x_1141_);
                                leanh::lean_ctor_set(v___x_1143_, 1, v___x_1142_);
                                v___x_1144_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1144_, 0, v___x_1143_);
                                v___x_1145_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_1138_,
                                    v_a_1137_,
                                    v___x_1144_,
                                    v___y_1071_,
                                    v___y_1072_,
                                    v___x_1097_,
                                    v___y_1074_,
                                );
                                leanh::lean_dec_ref(v___x_1097_);
                                return v___x_1145_;
                            } else {
                                leanh::lean_dec(v_a_1099_);
                                leanh::lean_dec_ref(v___x_1097_);
                                v_a_1146_ = leanh::lean_ctor_get(v___x_1136_, 0);
                                v_isSharedCheck_1153_ =
                                    (!leanh::lean_is_exclusive(v___x_1136_)) as u8;
                                if v_isSharedCheck_1153_ == 0 {
                                    v___x_1148_ = v___x_1136_;
                                    v_isShared_1149_ = v_isSharedCheck_1153_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1146_);
                                    leanh::lean_dec(v___x_1136_);
                                    v___x_1148_ = leanh::lean_box(0);
                                    v_isShared_1149_ = v_isSharedCheck_1153_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1097_);
                    v_a_1154_ = leanh::lean_ctor_get(v___x_1098_, 0);
                    v_isSharedCheck_1161_ = (!leanh::lean_is_exclusive(v___x_1098_)) as u8;
                    if v_isSharedCheck_1161_ == 0 {
                        v___x_1156_ = v___x_1098_;
                        v_isShared_1157_ = v_isSharedCheck_1161_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1154_);
                        leanh::lean_dec(v___x_1098_);
                        v___x_1156_ = leanh::lean_box(0);
                        v_isShared_1157_ = v_isSharedCheck_1161_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_fvarId_1105_);
                v___x_1118_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_zetaDeltaLocalDecl___boxed as *mut core::ffi::c_void,
                    11,
                    1,
                );
                leanh::lean_closure_set(v___x_1118_, 0, v_fvarId_1105_);
                v___x_1119_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_zetaDeltaTarget___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                leanh::lean_closure_set(v___x_1119_, 0, v_fvarId_1105_);
                v___x_1120_ = l_Lean_Elab_Tactic_withLocation(
                    v_loc_1065_,
                    v___x_1118_,
                    v___x_1119_,
                    v___f_1108_,
                    v___y_1110_,
                    v___y_1111_,
                    v___y_1112_,
                    v___y_1113_,
                    v___y_1114_,
                    v___y_1115_,
                    v___y_1116_,
                    v___y_1117_,
                );
                leanh::lean_dec_ref(v___y_1116_);
                return v___x_1120_;
            }
            4 => {
                if v_isShared_1131_ == 0 {
                    v___x_1133_ = v___x_1130_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1134_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
                    v___x_1133_ = v_reuseFailAlloc_1134_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1133_;
            }
            6 => {
                if v_isShared_1149_ == 0 {
                    v___x_1151_ = v___x_1148_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1152_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
                    v___x_1151_ = v_reuseFailAlloc_1152_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1151_;
            }
            8 => {
                if v_isShared_1157_ == 0 {
                    v___x_1159_ = v___x_1156_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1160_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
                    v___x_1159_ = v_reuseFailAlloc_1160_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___boxed(
    mut v_declNameId_1164_: *mut leanh::LeanObject,
    mut v___x_1165_: *mut leanh::LeanObject,
    mut v_loc_1166_: *mut leanh::LeanObject,
    mut v___x_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
    mut v___y_1170_: *mut leanh::LeanObject,
    mut v___y_1171_: *mut leanh::LeanObject,
    mut v___y_1172_: *mut leanh::LeanObject,
    mut v___y_1173_: *mut leanh::LeanObject,
    mut v___y_1174_: *mut leanh::LeanObject,
    mut v___y_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5515__boxed_1177_: u8 = 0;
    let mut v_res_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5515__boxed_1177_ = (leanh::lean_unbox(v___x_1167_) as u8);
    v_res_1178_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2(
        v_declNameId_1164_,
        v___x_1165_,
        v_loc_1166_,
        v___x_5515__boxed_1177_,
        v___y_1168_,
        v___y_1169_,
        v___y_1170_,
        v___y_1171_,
        v___y_1172_,
        v___y_1173_,
        v___y_1174_,
        v___y_1175_,
    );
    leanh::lean_dec(v___y_1175_);
    leanh::lean_dec(v___y_1173_);
    leanh::lean_dec_ref(v___y_1172_);
    leanh::lean_dec(v___y_1171_);
    leanh::lean_dec_ref(v___y_1170_);
    leanh::lean_dec(v___y_1169_);
    leanh::lean_dec_ref(v___y_1168_);
    leanh::lean_dec(v_loc_1166_);
    leanh::lean_dec(v_declNameId_1164_);
    return v_res_1178_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go(
    mut v_declNameId_1179_: *mut leanh::LeanObject,
    mut v_loc_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
    mut v_a_1182_: *mut leanh::LeanObject,
    mut v_a_1183_: *mut leanh::LeanObject,
    mut v_a_1184_: *mut leanh::LeanObject,
    mut v_a_1185_: *mut leanh::LeanObject,
    mut v_a_1186_: *mut leanh::LeanObject,
    mut v_a_1187_: *mut leanh::LeanObject,
    mut v_a_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = 0;
    v___x_1191_ = leanh::lean_box((v___x_1190_) as usize);
    leanh::lean_inc(v_declNameId_1179_);
    v___x_1192_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_elabTermForApply___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    leanh::lean_closure_set(v___x_1192_, 0, v_declNameId_1179_);
    leanh::lean_closure_set(v___x_1192_, 1, v___x_1191_);
    v___x_1193_ = leanh::lean_box((v___x_1190_) as usize);
    v___f_1194_ = leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___boxed
            as *mut core::ffi::c_void,
        13,
        4,
    );
    leanh::lean_closure_set(v___f_1194_, 0, v_declNameId_1179_);
    leanh::lean_closure_set(v___f_1194_, 1, v___x_1192_);
    leanh::lean_closure_set(v___f_1194_, 2, v_loc_1180_);
    leanh::lean_closure_set(v___f_1194_, 3, v___x_1193_);
    v___x_1195_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_1194_,
        v_a_1181_,
        v_a_1182_,
        v_a_1183_,
        v_a_1184_,
        v_a_1185_,
        v_a_1186_,
        v_a_1187_,
        v_a_1188_,
    );
    return v___x_1195_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___boxed(
    mut v_declNameId_1196_: *mut leanh::LeanObject,
    mut v_loc_1197_: *mut leanh::LeanObject,
    mut v_a_1198_: *mut leanh::LeanObject,
    mut v_a_1199_: *mut leanh::LeanObject,
    mut v_a_1200_: *mut leanh::LeanObject,
    mut v_a_1201_: *mut leanh::LeanObject,
    mut v_a_1202_: *mut leanh::LeanObject,
    mut v_a_1203_: *mut leanh::LeanObject,
    mut v_a_1204_: *mut leanh::LeanObject,
    mut v_a_1205_: *mut leanh::LeanObject,
    mut v_a_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go(
        v_declNameId_1196_,
        v_loc_1197_,
        v_a_1198_,
        v_a_1199_,
        v_a_1200_,
        v_a_1201_,
        v_a_1202_,
        v_a_1203_,
        v_a_1204_,
        v_a_1205_,
    );
    leanh::lean_dec(v_a_1205_);
    leanh::lean_dec_ref(v_a_1204_);
    leanh::lean_dec(v_a_1203_);
    leanh::lean_dec_ref(v_a_1202_);
    leanh::lean_dec(v_a_1201_);
    leanh::lean_dec_ref(v_a_1200_);
    leanh::lean_dec(v_a_1199_);
    leanh::lean_dec_ref(v_a_1198_);
    return v_res_1207_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0(
    mut v_00_u03b1_1208_: *mut leanh::LeanObject,
    mut v_msg_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
    mut v___y_1211_: *mut leanh::LeanObject,
    mut v___y_1212_: *mut leanh::LeanObject,
    mut v___y_1213_: *mut leanh::LeanObject,
    mut v___y_1214_: *mut leanh::LeanObject,
    mut v___y_1215_: *mut leanh::LeanObject,
    mut v___y_1216_: *mut leanh::LeanObject,
    mut v___y_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v_msg_1209_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
    return v___x_1219_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___boxed(
    mut v_00_u03b1_1220_: *mut leanh::LeanObject,
    mut v_msg_1221_: *mut leanh::LeanObject,
    mut v___y_1222_: *mut leanh::LeanObject,
    mut v___y_1223_: *mut leanh::LeanObject,
    mut v___y_1224_: *mut leanh::LeanObject,
    mut v___y_1225_: *mut leanh::LeanObject,
    mut v___y_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
    mut v___y_1228_: *mut leanh::LeanObject,
    mut v___y_1229_: *mut leanh::LeanObject,
    mut v___y_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1231_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0(v_00_u03b1_1220_, v_msg_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
    leanh::lean_dec(v___y_1229_);
    leanh::lean_dec_ref(v___y_1228_);
    leanh::lean_dec(v___y_1227_);
    leanh::lean_dec_ref(v___y_1226_);
    leanh::lean_dec(v___y_1225_);
    leanh::lean_dec_ref(v___y_1224_);
    leanh::lean_dec(v___y_1223_);
    leanh::lean_dec_ref(v___y_1222_);
    return v_res_1231_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(
    mut v_loc_1232_: *mut leanh::LeanObject,
    mut v_as_1233_: *mut leanh::LeanObject,
    mut v_sz_1234_: usize,
    mut v_i_1235_: usize,
    mut v_b_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
    mut v___y_1243_: *mut leanh::LeanObject,
    mut v___y_1244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1246_: u8 = 0;
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: usize = 0;
    let mut v___x_1252_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1246_ = lean_usize_dec_lt(v_i_1235_, v_sz_1234_);
                if v___x_1246_ == 0 {
                    leanh::lean_dec(v_loc_1232_);
                    v___x_1247_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1247_, 0, v_b_1236_);
                    return v___x_1247_;
                } else {
                    v_a_1248_ = lean_array_uget_borrowed(v_as_1233_, v_i_1235_);
                    leanh::lean_inc(v_loc_1232_);
                    leanh::lean_inc(v_a_1248_);
                    v___x_1249_ =
                        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go(
                            v_a_1248_,
                            v_loc_1232_,
                            v___y_1237_,
                            v___y_1238_,
                            v___y_1239_,
                            v___y_1240_,
                            v___y_1241_,
                            v___y_1242_,
                            v___y_1243_,
                            v___y_1244_,
                        );
                    if leanh::lean_obj_tag(v___x_1249_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1249_, 1);
                        v___x_1250_ = leanh::lean_box(0);
                        v___x_1251_ = 1usize;
                        v___x_1252_ = lean_usize_add(v_i_1235_, v___x_1251_);
                        v_i_1235_ = v___x_1252_;
                        v_b_1236_ = v___x_1250_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_loc_1232_);
                        return v___x_1249_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0___boxed(
    mut v_loc_1254_: *mut leanh::LeanObject,
    mut v_as_1255_: *mut leanh::LeanObject,
    mut v_sz_1256_: *mut leanh::LeanObject,
    mut v_i_1257_: *mut leanh::LeanObject,
    mut v_b_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1268_: usize = 0;
    let mut v_i_boxed_1269_: usize = 0;
    let mut v_res_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1268_ = leanh::lean_unbox_usize(v_sz_1256_);
    leanh::lean_dec(v_sz_1256_);
    v_i_boxed_1269_ = leanh::lean_unbox_usize(v_i_1257_);
    leanh::lean_dec(v_i_1257_);
    v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(v_loc_1254_, v_as_1255_, v_sz_boxed_1268_, v_i_boxed_1269_, v_b_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
    leanh::lean_dec(v___y_1266_);
    leanh::lean_dec_ref(v___y_1265_);
    leanh::lean_dec(v___y_1264_);
    leanh::lean_dec_ref(v___y_1263_);
    leanh::lean_dec(v___y_1262_);
    leanh::lean_dec_ref(v___y_1261_);
    leanh::lean_dec(v___y_1260_);
    leanh::lean_dec_ref(v___y_1259_);
    leanh::lean_dec_ref(v_as_1255_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalUnfold(
    mut v_stx_1271_: *mut leanh::LeanObject,
    mut v_a_1272_: *mut leanh::LeanObject,
    mut v_a_1273_: *mut leanh::LeanObject,
    mut v_a_1274_: *mut leanh::LeanObject,
    mut v_a_1275_: *mut leanh::LeanObject,
    mut v_a_1276_: *mut leanh::LeanObject,
    mut v_a_1277_: *mut leanh::LeanObject,
    mut v_a_1278_: *mut leanh::LeanObject,
    mut v_a_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1288_: usize = 0;
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1293_: u8 = 0;
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut v_unused_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1281_ = leanh::lean_unsigned_to_nat(2);
                v___x_1282_ = l_Lean_Syntax_getArg(v_stx_1271_, v___x_1281_);
                v_loc_1283_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1282_);
                leanh::lean_dec(v___x_1282_);
                v___x_1284_ = leanh::lean_unsigned_to_nat(1);
                v___x_1285_ = l_Lean_Syntax_getArg(v_stx_1271_, v___x_1284_);
                v___x_1286_ = l_Lean_Syntax_getArgs(v___x_1285_);
                leanh::lean_dec(v___x_1285_);
                v___x_1287_ = leanh::lean_box(0);
                v_sz_1288_ = lean_array_size(v___x_1286_);
                v___x_1289_ = 0usize;
                v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(v_loc_1283_, v___x_1286_, v_sz_1288_, v___x_1289_, v___x_1287_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
                leanh::lean_dec_ref(v___x_1286_);
                if leanh::lean_obj_tag(v___x_1290_) == 0 {
                    v_isSharedCheck_1297_ = (!leanh::lean_is_exclusive(v___x_1290_)) as u8;
                    if v_isSharedCheck_1297_ == 0 {
                        v_unused_1298_ = leanh::lean_ctor_get(v___x_1290_, 0);
                        leanh::lean_dec(v_unused_1298_);
                        v___x_1292_ = v___x_1290_;
                        v_isShared_1293_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1290_);
                        v___x_1292_ = leanh::lean_box(0);
                        v_isShared_1293_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1290_;
                }
            }
            1 => {
                if v_isShared_1293_ == 0 {
                    leanh::lean_ctor_set(v___x_1292_, 0, v___x_1287_);
                    v___x_1295_ = v___x_1292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1287_);
                    v___x_1295_ = v_reuseFailAlloc_1296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalUnfold___boxed(
    mut v_stx_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
    mut v_a_1301_: *mut leanh::LeanObject,
    mut v_a_1302_: *mut leanh::LeanObject,
    mut v_a_1303_: *mut leanh::LeanObject,
    mut v_a_1304_: *mut leanh::LeanObject,
    mut v_a_1305_: *mut leanh::LeanObject,
    mut v_a_1306_: *mut leanh::LeanObject,
    mut v_a_1307_: *mut leanh::LeanObject,
    mut v_a_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1309_ = l_Lean_Elab_Tactic_evalUnfold(
        v_stx_1299_,
        v_a_1300_,
        v_a_1301_,
        v_a_1302_,
        v_a_1303_,
        v_a_1304_,
        v_a_1305_,
        v_a_1306_,
        v_a_1307_,
    );
    leanh::lean_dec(v_a_1307_);
    leanh::lean_dec_ref(v_a_1306_);
    leanh::lean_dec(v_a_1305_);
    leanh::lean_dec_ref(v_a_1304_);
    leanh::lean_dec(v_a_1303_);
    leanh::lean_dec_ref(v_a_1302_);
    leanh::lean_dec(v_a_1301_);
    leanh::lean_dec_ref(v_a_1300_);
    leanh::lean_dec(v_stx_1299_);
    return v_res_1309_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1()
-> *mut leanh::LeanObject {
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1326_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1327_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3;
    v___x_1328_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6;
    v___x_1329_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalUnfold___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1330_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1326_,
        v___x_1327_,
        v___x_1328_,
        v___x_1329_,
    );
    return v___x_1330_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___boxed(
    mut v_a_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1332_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1();
    return v_res_1332_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3()
-> *mut leanh::LeanObject {
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1335_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6;
    v___x_1336_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0;
    v___x_1337_ = l_Lean_addBuiltinDocString(v___x_1335_, v___x_1336_);
    return v___x_1337_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___boxed(
    mut v_a_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1339_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3();
    return v_res_1339_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5()
-> *mut leanh::LeanObject {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6;
    v___x_1367_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6;
    v___x_1368_ = l_Lean_addBuiltinDeclarationRanges(v___x_1366_, v___x_1367_);
    return v___x_1368_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___boxed(
    mut v_a_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1370_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5();
    return v_res_1370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Unfold(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Unfold(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Unfold(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Unfold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Unfold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Unfold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Unfold(builtin);
}