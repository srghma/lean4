// Lean compiler output
// Module: Lean.Elab.Tactic.Unfold
// Imports: Lean.Meta.Tactic.Unfold Lean.Elab.Tactic.Location
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_replaceRef,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 110, 102, 111, 108, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value) as *mut LeanObject,13034500471729497529 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 105, 100, 32, 110, 111, 116, 32, 117, 110, 102, 111, 108, 100, 32, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [84, 97, 99, 116, 105, 99, 32, 96, 117, 110, 102, 111, 108, 100, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 76, 111, 99, 97, 108, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 104, 97, 115, 32, 110, 111, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 103, 108, 111, 98, 97, 108, 32, 111, 114, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value) as *mut LeanObject,18259345790759314728 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 85, 110, 102, 111, 108, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value) as *mut LeanObject,3655951909266319154 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [34, 117, 110, 102, 111, 108, 100, 32, 34, 32, 105, 100, 101, 110, 116, 43, 32, 40, 108, 111, 99, 97, 116, 105, 111, 110, 41, 63, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut LeanObject,((( 129 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value) as *mut LeanObject,((( 129 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(
    mut v_declName_686_: *mut LeanObject,
    mut v_fvarId_687_: *mut LeanObject,
    mut v_a_688_: *mut LeanObject,
    mut v_a_689_: *mut LeanObject,
    mut v_a_690_: *mut LeanObject,
    mut v_a_691_: *mut LeanObject,
    mut v_a_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_a_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_694_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_,
                );
                if lean_obj_tag(v___x_694_) == 0 {
                    v_a_695_ = lean_ctor_get(v___x_694_, 0);
                    lean_inc(v_a_695_);
                    lean_dec_ref_known(v___x_694_, 1);
                    v___x_696_ = l_Lean_Meta_unfoldLocalDecl(
                        v_a_695_,
                        v_fvarId_687_,
                        v_declName_686_,
                        v_a_689_,
                        v_a_690_,
                        v_a_691_,
                        v_a_692_,
                    );
                    if lean_obj_tag(v___x_696_) == 0 {
                        v_a_697_ = lean_ctor_get(v___x_696_, 0);
                        lean_inc(v_a_697_);
                        lean_dec_ref_known(v___x_696_, 1);
                        v___x_698_ = lean_box(0);
                        v___x_699_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_699_, 0, v_a_697_);
                        lean_ctor_set(v___x_699_, 1, v___x_698_);
                        v___x_700_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_699_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_,
                        );
                        return v___x_700_;
                    } else {
                        v_a_701_ = lean_ctor_get(v___x_696_, 0);
                        v_isSharedCheck_708_ = (!lean_is_exclusive(v___x_696_)) as u8;
                        if v_isSharedCheck_708_ == 0 {
                            v___x_703_ = v___x_696_;
                            v_isShared_704_ = v_isSharedCheck_708_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_701_);
                            lean_dec(v___x_696_);
                            v___x_703_ = lean_box(0);
                            v_isShared_704_ = v_isSharedCheck_708_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fvarId_687_);
                    lean_dec(v_declName_686_);
                    v_a_709_ = lean_ctor_get(v___x_694_, 0);
                    v_isSharedCheck_716_ = (!lean_is_exclusive(v___x_694_)) as u8;
                    if v_isSharedCheck_716_ == 0 {
                        v___x_711_ = v___x_694_;
                        v_isShared_712_ = v_isSharedCheck_716_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_709_);
                        lean_dec(v___x_694_);
                        v___x_711_ = lean_box(0);
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
                    v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
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
                    v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
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
    mut v_declName_717_: *mut LeanObject,
    mut v_fvarId_718_: *mut LeanObject,
    mut v_a_719_: *mut LeanObject,
    mut v_a_720_: *mut LeanObject,
    mut v_a_721_: *mut LeanObject,
    mut v_a_722_: *mut LeanObject,
    mut v_a_723_: *mut LeanObject,
    mut v_a_724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_725_: *mut LeanObject = core::ptr::null_mut();
    v_res_725_ = l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(
        v_declName_717_,
        v_fvarId_718_,
        v_a_719_,
        v_a_720_,
        v_a_721_,
        v_a_722_,
        v_a_723_,
    );
    lean_dec(v_a_723_);
    lean_dec_ref(v_a_722_);
    lean_dec(v_a_721_);
    lean_dec_ref(v_a_720_);
    lean_dec(v_a_719_);
    return v_res_725_;
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldLocalDecl(
    mut v_declName_726_: *mut LeanObject,
    mut v_fvarId_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_a_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_declName_738_: *mut LeanObject,
    mut v_fvarId_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
    mut v_a_744_: *mut LeanObject,
    mut v_a_745_: *mut LeanObject,
    mut v_a_746_: *mut LeanObject,
    mut v_a_747_: *mut LeanObject,
    mut v_a_748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_749_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_747_);
    lean_dec_ref(v_a_746_);
    lean_dec(v_a_745_);
    lean_dec_ref(v_a_744_);
    lean_dec(v_a_743_);
    lean_dec_ref(v_a_742_);
    lean_dec(v_a_741_);
    lean_dec_ref(v_a_740_);
    return v_res_749_;
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldTarget___redArg(
    mut v_declName_750_: *mut LeanObject,
    mut v_a_751_: *mut LeanObject,
    mut v_a_752_: *mut LeanObject,
    mut v_a_753_: *mut LeanObject,
    mut v_a_754_: *mut LeanObject,
    mut v_a_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_767_: u8 = 0;
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_771_: u8 = 0;
    let mut v_a_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_775_: u8 = 0;
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_757_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_,
                );
                if lean_obj_tag(v___x_757_) == 0 {
                    v_a_758_ = lean_ctor_get(v___x_757_, 0);
                    lean_inc(v_a_758_);
                    lean_dec_ref_known(v___x_757_, 1);
                    v___x_759_ = l_Lean_Meta_unfoldTarget(
                        v_a_758_,
                        v_declName_750_,
                        v_a_752_,
                        v_a_753_,
                        v_a_754_,
                        v_a_755_,
                    );
                    if lean_obj_tag(v___x_759_) == 0 {
                        v_a_760_ = lean_ctor_get(v___x_759_, 0);
                        lean_inc(v_a_760_);
                        lean_dec_ref_known(v___x_759_, 1);
                        v___x_761_ = lean_box(0);
                        v___x_762_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_762_, 0, v_a_760_);
                        lean_ctor_set(v___x_762_, 1, v___x_761_);
                        v___x_763_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_762_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_,
                        );
                        return v___x_763_;
                    } else {
                        v_a_764_ = lean_ctor_get(v___x_759_, 0);
                        v_isSharedCheck_771_ = (!lean_is_exclusive(v___x_759_)) as u8;
                        if v_isSharedCheck_771_ == 0 {
                            v___x_766_ = v___x_759_;
                            v_isShared_767_ = v_isSharedCheck_771_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_764_);
                            lean_dec(v___x_759_);
                            v___x_766_ = lean_box(0);
                            v_isShared_767_ = v_isSharedCheck_771_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_750_);
                    v_a_772_ = lean_ctor_get(v___x_757_, 0);
                    v_isSharedCheck_779_ = (!lean_is_exclusive(v___x_757_)) as u8;
                    if v_isSharedCheck_779_ == 0 {
                        v___x_774_ = v___x_757_;
                        v_isShared_775_ = v_isSharedCheck_779_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_772_);
                        lean_dec(v___x_757_);
                        v___x_774_ = lean_box(0);
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
                    v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
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
                    v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
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
    mut v_declName_780_: *mut LeanObject,
    mut v_a_781_: *mut LeanObject,
    mut v_a_782_: *mut LeanObject,
    mut v_a_783_: *mut LeanObject,
    mut v_a_784_: *mut LeanObject,
    mut v_a_785_: *mut LeanObject,
    mut v_a_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_787_: *mut LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Lean_Elab_Tactic_unfoldTarget___redArg(
        v_declName_780_,
        v_a_781_,
        v_a_782_,
        v_a_783_,
        v_a_784_,
        v_a_785_,
    );
    lean_dec(v_a_785_);
    lean_dec_ref(v_a_784_);
    lean_dec(v_a_783_);
    lean_dec_ref(v_a_782_);
    lean_dec(v_a_781_);
    return v_res_787_;
}
pub unsafe fn l_Lean_Elab_Tactic_unfoldTarget(
    mut v_declName_788_: *mut LeanObject,
    mut v_a_789_: *mut LeanObject,
    mut v_a_790_: *mut LeanObject,
    mut v_a_791_: *mut LeanObject,
    mut v_a_792_: *mut LeanObject,
    mut v_a_793_: *mut LeanObject,
    mut v_a_794_: *mut LeanObject,
    mut v_a_795_: *mut LeanObject,
    mut v_a_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_declName_799_: *mut LeanObject,
    mut v_a_800_: *mut LeanObject,
    mut v_a_801_: *mut LeanObject,
    mut v_a_802_: *mut LeanObject,
    mut v_a_803_: *mut LeanObject,
    mut v_a_804_: *mut LeanObject,
    mut v_a_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
    mut v_a_808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_809_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_807_);
    lean_dec_ref(v_a_806_);
    lean_dec(v_a_805_);
    lean_dec_ref(v_a_804_);
    lean_dec(v_a_803_);
    lean_dec_ref(v_a_802_);
    lean_dec(v_a_801_);
    lean_dec_ref(v_a_800_);
    return v_res_809_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(
    mut v_declFVarId_810_: *mut LeanObject,
    mut v_fvarId_811_: *mut LeanObject,
    mut v_a_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_a_814_: *mut LeanObject,
    mut v_a_815_: *mut LeanObject,
    mut v_a_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_828_: u8 = 0;
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut v_a_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_818_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_,
                );
                if lean_obj_tag(v___x_818_) == 0 {
                    v_a_819_ = lean_ctor_get(v___x_818_, 0);
                    lean_inc(v_a_819_);
                    lean_dec_ref_known(v___x_818_, 1);
                    v___x_820_ = l_Lean_Meta_zetaDeltaLocalDecl(
                        v_a_819_,
                        v_fvarId_811_,
                        v_declFVarId_810_,
                        v_a_813_,
                        v_a_814_,
                        v_a_815_,
                        v_a_816_,
                    );
                    if lean_obj_tag(v___x_820_) == 0 {
                        v_a_821_ = lean_ctor_get(v___x_820_, 0);
                        lean_inc(v_a_821_);
                        lean_dec_ref_known(v___x_820_, 1);
                        v___x_822_ = lean_box(0);
                        v___x_823_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_823_, 0, v_a_821_);
                        lean_ctor_set(v___x_823_, 1, v___x_822_);
                        v___x_824_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_823_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_,
                        );
                        return v___x_824_;
                    } else {
                        v_a_825_ = lean_ctor_get(v___x_820_, 0);
                        v_isSharedCheck_832_ = (!lean_is_exclusive(v___x_820_)) as u8;
                        if v_isSharedCheck_832_ == 0 {
                            v___x_827_ = v___x_820_;
                            v_isShared_828_ = v_isSharedCheck_832_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_825_);
                            lean_dec(v___x_820_);
                            v___x_827_ = lean_box(0);
                            v_isShared_828_ = v_isSharedCheck_832_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fvarId_811_);
                    lean_dec(v_declFVarId_810_);
                    v_a_833_ = lean_ctor_get(v___x_818_, 0);
                    v_isSharedCheck_840_ = (!lean_is_exclusive(v___x_818_)) as u8;
                    if v_isSharedCheck_840_ == 0 {
                        v___x_835_ = v___x_818_;
                        v_isShared_836_ = v_isSharedCheck_840_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_833_);
                        lean_dec(v___x_818_);
                        v___x_835_ = lean_box(0);
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
                    v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
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
                    v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
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
    mut v_declFVarId_841_: *mut LeanObject,
    mut v_fvarId_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
    mut v_a_846_: *mut LeanObject,
    mut v_a_847_: *mut LeanObject,
    mut v_a_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_849_: *mut LeanObject = core::ptr::null_mut();
    v_res_849_ = l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(
        v_declFVarId_841_,
        v_fvarId_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
        v_a_847_,
    );
    lean_dec(v_a_847_);
    lean_dec_ref(v_a_846_);
    lean_dec(v_a_845_);
    lean_dec_ref(v_a_844_);
    lean_dec(v_a_843_);
    return v_res_849_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaLocalDecl(
    mut v_declFVarId_850_: *mut LeanObject,
    mut v_fvarId_851_: *mut LeanObject,
    mut v_a_852_: *mut LeanObject,
    mut v_a_853_: *mut LeanObject,
    mut v_a_854_: *mut LeanObject,
    mut v_a_855_: *mut LeanObject,
    mut v_a_856_: *mut LeanObject,
    mut v_a_857_: *mut LeanObject,
    mut v_a_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_declFVarId_862_: *mut LeanObject,
    mut v_fvarId_863_: *mut LeanObject,
    mut v_a_864_: *mut LeanObject,
    mut v_a_865_: *mut LeanObject,
    mut v_a_866_: *mut LeanObject,
    mut v_a_867_: *mut LeanObject,
    mut v_a_868_: *mut LeanObject,
    mut v_a_869_: *mut LeanObject,
    mut v_a_870_: *mut LeanObject,
    mut v_a_871_: *mut LeanObject,
    mut v_a_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_873_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_871_);
    lean_dec_ref(v_a_870_);
    lean_dec(v_a_869_);
    lean_dec_ref(v_a_868_);
    lean_dec(v_a_867_);
    lean_dec_ref(v_a_866_);
    lean_dec(v_a_865_);
    lean_dec_ref(v_a_864_);
    return v_res_873_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(
    mut v_declFVarId_874_: *mut LeanObject,
    mut v_a_875_: *mut LeanObject,
    mut v_a_876_: *mut LeanObject,
    mut v_a_877_: *mut LeanObject,
    mut v_a_878_: *mut LeanObject,
    mut v_a_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v_a_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_881_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_,
                );
                if lean_obj_tag(v___x_881_) == 0 {
                    v_a_882_ = lean_ctor_get(v___x_881_, 0);
                    lean_inc(v_a_882_);
                    lean_dec_ref_known(v___x_881_, 1);
                    v___x_883_ = l_Lean_Meta_zetaDeltaTarget(
                        v_a_882_,
                        v_declFVarId_874_,
                        v_a_876_,
                        v_a_877_,
                        v_a_878_,
                        v_a_879_,
                    );
                    if lean_obj_tag(v___x_883_) == 0 {
                        v_a_884_ = lean_ctor_get(v___x_883_, 0);
                        lean_inc(v_a_884_);
                        lean_dec_ref_known(v___x_883_, 1);
                        v___x_885_ = lean_box(0);
                        v___x_886_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_886_, 0, v_a_884_);
                        lean_ctor_set(v___x_886_, 1, v___x_885_);
                        v___x_887_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_886_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_,
                        );
                        return v___x_887_;
                    } else {
                        v_a_888_ = lean_ctor_get(v___x_883_, 0);
                        v_isSharedCheck_895_ = (!lean_is_exclusive(v___x_883_)) as u8;
                        if v_isSharedCheck_895_ == 0 {
                            v___x_890_ = v___x_883_;
                            v_isShared_891_ = v_isSharedCheck_895_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_888_);
                            lean_dec(v___x_883_);
                            v___x_890_ = lean_box(0);
                            v_isShared_891_ = v_isSharedCheck_895_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declFVarId_874_);
                    v_a_896_ = lean_ctor_get(v___x_881_, 0);
                    v_isSharedCheck_903_ = (!lean_is_exclusive(v___x_881_)) as u8;
                    if v_isSharedCheck_903_ == 0 {
                        v___x_898_ = v___x_881_;
                        v_isShared_899_ = v_isSharedCheck_903_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_896_);
                        lean_dec(v___x_881_);
                        v___x_898_ = lean_box(0);
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
                    v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
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
                    v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
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
    mut v_declFVarId_904_: *mut LeanObject,
    mut v_a_905_: *mut LeanObject,
    mut v_a_906_: *mut LeanObject,
    mut v_a_907_: *mut LeanObject,
    mut v_a_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
    mut v_a_910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_911_: *mut LeanObject = core::ptr::null_mut();
    v_res_911_ = l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(
        v_declFVarId_904_,
        v_a_905_,
        v_a_906_,
        v_a_907_,
        v_a_908_,
        v_a_909_,
    );
    lean_dec(v_a_909_);
    lean_dec_ref(v_a_908_);
    lean_dec(v_a_907_);
    lean_dec_ref(v_a_906_);
    lean_dec(v_a_905_);
    return v_res_911_;
}
pub unsafe fn l_Lean_Elab_Tactic_zetaDeltaTarget(
    mut v_declFVarId_912_: *mut LeanObject,
    mut v_a_913_: *mut LeanObject,
    mut v_a_914_: *mut LeanObject,
    mut v_a_915_: *mut LeanObject,
    mut v_a_916_: *mut LeanObject,
    mut v_a_917_: *mut LeanObject,
    mut v_a_918_: *mut LeanObject,
    mut v_a_919_: *mut LeanObject,
    mut v_a_920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_declFVarId_923_: *mut LeanObject,
    mut v_a_924_: *mut LeanObject,
    mut v_a_925_: *mut LeanObject,
    mut v_a_926_: *mut LeanObject,
    mut v_a_927_: *mut LeanObject,
    mut v_a_928_: *mut LeanObject,
    mut v_a_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_a_931_: *mut LeanObject,
    mut v_a_932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_933_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_931_);
    lean_dec_ref(v_a_930_);
    lean_dec(v_a_929_);
    lean_dec_ref(v_a_928_);
    lean_dec(v_a_927_);
    lean_dec_ref(v_a_926_);
    lean_dec(v_a_925_);
    lean_dec_ref(v_a_924_);
    return v_res_933_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    v___x_938_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2;
    v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
    return v___x_939_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    v___x_941_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4;
    v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
    return v___x_942_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0(
    mut v_declName_943_: *mut LeanObject,
    mut v_x_944_: *mut LeanObject,
    mut v___y_945_: *mut LeanObject,
    mut v___y_946_: *mut LeanObject,
    mut v___y_947_: *mut LeanObject,
    mut v___y_948_: *mut LeanObject,
    mut v___y_949_: *mut LeanObject,
    mut v___y_950_: *mut LeanObject,
    mut v___y_951_: *mut LeanObject,
    mut v___y_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    v___x_954_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1;
    v___x_955_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3);
    v___x_956_ = l_Lean_MessageData_ofName(v_declName_943_);
    v___x_957_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_957_, 0, v___x_955_);
    lean_ctor_set(v___x_957_, 1, v___x_956_);
    v___x_958_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5);
    v___x_959_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_959_, 0, v___x_957_);
    lean_ctor_set(v___x_959_, 1, v___x_958_);
    v___x_960_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_960_, 0, v___x_959_);
    v___x_961_ = l_Lean_Meta_throwTacticEx___redArg(
        v___x_954_, v_x_944_, v___x_960_, v___y_949_, v___y_950_, v___y_951_, v___y_952_,
    );
    return v___x_961_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___boxed(
    mut v_declName_962_: *mut LeanObject,
    mut v_x_963_: *mut LeanObject,
    mut v___y_964_: *mut LeanObject,
    mut v___y_965_: *mut LeanObject,
    mut v___y_966_: *mut LeanObject,
    mut v___y_967_: *mut LeanObject,
    mut v___y_968_: *mut LeanObject,
    mut v___y_969_: *mut LeanObject,
    mut v___y_970_: *mut LeanObject,
    mut v___y_971_: *mut LeanObject,
    mut v___y_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_973_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_971_);
    lean_dec_ref(v___y_970_);
    lean_dec(v___y_969_);
    lean_dec_ref(v___y_968_);
    lean_dec(v___y_967_);
    lean_dec_ref(v___y_966_);
    lean_dec(v___y_965_);
    lean_dec_ref(v___y_964_);
    return v_res_973_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1(
    mut v_a_974_: *mut LeanObject,
    mut v_x_975_: *mut LeanObject,
    mut v___y_976_: *mut LeanObject,
    mut v___y_977_: *mut LeanObject,
    mut v___y_978_: *mut LeanObject,
    mut v___y_979_: *mut LeanObject,
    mut v___y_980_: *mut LeanObject,
    mut v___y_981_: *mut LeanObject,
    mut v___y_982_: *mut LeanObject,
    mut v___y_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    v___x_985_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1;
    v___x_986_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3);
    v___x_987_ = l_Lean_MessageData_ofExpr(v_a_974_);
    v___x_988_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_988_, 0, v___x_986_);
    lean_ctor_set(v___x_988_, 1, v___x_987_);
    v___x_989_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5);
    v___x_990_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_990_, 0, v___x_988_);
    lean_ctor_set(v___x_990_, 1, v___x_989_);
    v___x_991_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_991_, 0, v___x_990_);
    v___x_992_ = l_Lean_Meta_throwTacticEx___redArg(
        v___x_985_, v_x_975_, v___x_991_, v___y_980_, v___y_981_, v___y_982_, v___y_983_,
    );
    return v___x_992_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1___boxed(
    mut v_a_993_: *mut LeanObject,
    mut v_x_994_: *mut LeanObject,
    mut v___y_995_: *mut LeanObject,
    mut v___y_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
    mut v___y_1001_: *mut LeanObject,
    mut v___y_1002_: *mut LeanObject,
    mut v___y_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1004_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1002_);
    lean_dec_ref(v___y_1001_);
    lean_dec(v___y_1000_);
    lean_dec_ref(v___y_999_);
    lean_dec(v___y_998_);
    lean_dec_ref(v___y_997_);
    lean_dec(v___y_996_);
    lean_dec_ref(v___y_995_);
    return v_res_1004_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(
    mut v_msgData_1005_: *mut LeanObject,
    mut v___y_1006_: *mut LeanObject,
    mut v___y_1007_: *mut LeanObject,
    mut v___y_1008_: *mut LeanObject,
    mut v___y_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    v___x_1011_ = lean_st_ref_get(v___y_1009_);
    v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
    lean_inc_ref(v_env_1012_);
    lean_dec(v___x_1011_);
    v___x_1013_ = lean_st_ref_get(v___y_1007_);
    v_mctx_1014_ = lean_ctor_get(v___x_1013_, 0);
    lean_inc_ref(v_mctx_1014_);
    lean_dec(v___x_1013_);
    v_lctx_1015_ = lean_ctor_get(v___y_1006_, 2);
    v_options_1016_ = lean_ctor_get(v___y_1008_, 2);
    lean_inc_ref(v_options_1016_);
    lean_inc_ref(v_lctx_1015_);
    v___x_1017_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1017_, 0, v_env_1012_);
    lean_ctor_set(v___x_1017_, 1, v_mctx_1014_);
    lean_ctor_set(v___x_1017_, 2, v_lctx_1015_);
    lean_ctor_set(v___x_1017_, 3, v_options_1016_);
    v___x_1018_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1018_, 0, v___x_1017_);
    lean_ctor_set(v___x_1018_, 1, v_msgData_1005_);
    v___x_1019_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    return v___x_1019_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0___boxed(
    mut v_msgData_1020_: *mut LeanObject,
    mut v___y_1021_: *mut LeanObject,
    mut v___y_1022_: *mut LeanObject,
    mut v___y_1023_: *mut LeanObject,
    mut v___y_1024_: *mut LeanObject,
    mut v___y_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1026_: *mut LeanObject = core::ptr::null_mut();
    v_res_1026_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(v_msgData_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
    lean_dec(v___y_1024_);
    lean_dec_ref(v___y_1023_);
    lean_dec(v___y_1022_);
    lean_dec_ref(v___y_1021_);
    return v_res_1026_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(
    mut v_msg_1027_: *mut LeanObject,
    mut v___y_1028_: *mut LeanObject,
    mut v___y_1029_: *mut LeanObject,
    mut v___y_1030_: *mut LeanObject,
    mut v___y_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1038_: u8 = 0;
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1033_ = lean_ctor_get(v___y_1030_, 5);
                v___x_1034_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(v_msg_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
                v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
                v_isSharedCheck_1043_ = (!lean_is_exclusive(v___x_1034_)) as u8;
                if v_isSharedCheck_1043_ == 0 {
                    v___x_1037_ = v___x_1034_;
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1035_);
                    lean_dec(v___x_1034_);
                    v___x_1037_ = lean_box(0);
                    v_isShared_1038_ = v_isSharedCheck_1043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1033_);
                v___x_1039_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1039_, 0, v_ref_1033_);
                lean_ctor_set(v___x_1039_, 1, v_a_1035_);
                if v_isShared_1038_ == 0 {
                    lean_ctor_set_tag(v___x_1037_, 1);
                    lean_ctor_set(v___x_1037_, 0, v___x_1039_);
                    v___x_1041_ = v___x_1037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
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
    mut v_msg_1044_: *mut LeanObject,
    mut v___y_1045_: *mut LeanObject,
    mut v___y_1046_: *mut LeanObject,
    mut v___y_1047_: *mut LeanObject,
    mut v___y_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v_msg_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
    lean_dec(v___y_1048_);
    lean_dec_ref(v___y_1047_);
    lean_dec(v___y_1046_);
    lean_dec_ref(v___y_1045_);
    return v_res_1050_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    v___x_1052_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0;
    v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
    return v___x_1053_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3()
-> *mut LeanObject {
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    v___x_1055_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2;
    v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
    return v___x_1056_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5()
-> *mut LeanObject {
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    v___x_1058_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4;
    v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
    return v___x_1059_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7()
-> *mut LeanObject {
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    v___x_1061_ =
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6;
    v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
    return v___x_1062_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2(
    mut v_declNameId_1063_: *mut LeanObject,
    mut v___x_1064_: *mut LeanObject,
    mut v_loc_1065_: *mut LeanObject,
    mut v___x_1066_: u8,
    mut v___y_1067_: *mut LeanObject,
    mut v___y_1068_: *mut LeanObject,
    mut v___y_1069_: *mut LeanObject,
    mut v___y_1070_: *mut LeanObject,
    mut v___y_1071_: *mut LeanObject,
    mut v___y_1072_: *mut LeanObject,
    mut v___y_1073_: *mut LeanObject,
    mut v___y_1074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1088_: u8 = 0;
    let mut v_cancelTk_x3f_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1090_: u8 = 0;
    let mut v_inheritedTraceOptions_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v_ref_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: u8 = 0;
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1131_: u8 = 0;
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1135_: u8 = 0;
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1149_: u8 = 0;
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1153_: u8 = 0;
    let mut v_a_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1161_: u8 = 0;
    let mut v_reuseFailAlloc_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_1076_ = lean_ctor_get(v___y_1073_, 0);
                v_fileMap_1077_ = lean_ctor_get(v___y_1073_, 1);
                v_options_1078_ = lean_ctor_get(v___y_1073_, 2);
                v_currRecDepth_1079_ = lean_ctor_get(v___y_1073_, 3);
                v_maxRecDepth_1080_ = lean_ctor_get(v___y_1073_, 4);
                v_ref_1081_ = lean_ctor_get(v___y_1073_, 5);
                v_currNamespace_1082_ = lean_ctor_get(v___y_1073_, 6);
                v_openDecls_1083_ = lean_ctor_get(v___y_1073_, 7);
                v_initHeartbeats_1084_ = lean_ctor_get(v___y_1073_, 8);
                v_maxHeartbeats_1085_ = lean_ctor_get(v___y_1073_, 9);
                v_quotContext_1086_ = lean_ctor_get(v___y_1073_, 10);
                v_currMacroScope_1087_ = lean_ctor_get(v___y_1073_, 11);
                v_diag_1088_ = lean_ctor_get_uint8(
                    v___y_1073_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1089_ = lean_ctor_get(v___y_1073_, 12);
                v_suppressElabErrors_1090_ = lean_ctor_get_uint8(
                    v___y_1073_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1091_ = lean_ctor_get(v___y_1073_, 13);
                v_isSharedCheck_1163_ = (!lean_is_exclusive(v___y_1073_)) as u8;
                if v_isSharedCheck_1163_ == 0 {
                    v___x_1093_ = v___y_1073_;
                    v_isShared_1094_ = v_isSharedCheck_1163_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_1091_);
                    lean_inc(v_cancelTk_x3f_1089_);
                    lean_inc(v_currMacroScope_1087_);
                    lean_inc(v_quotContext_1086_);
                    lean_inc(v_maxHeartbeats_1085_);
                    lean_inc(v_initHeartbeats_1084_);
                    lean_inc(v_openDecls_1083_);
                    lean_inc(v_currNamespace_1082_);
                    lean_inc(v_ref_1081_);
                    lean_inc(v_maxRecDepth_1080_);
                    lean_inc(v_currRecDepth_1079_);
                    lean_inc(v_options_1078_);
                    lean_inc(v_fileMap_1077_);
                    lean_inc(v_fileName_1076_);
                    lean_dec(v___y_1073_);
                    v___x_1093_ = lean_box(0);
                    v_isShared_1094_ = v_isSharedCheck_1163_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_1095_ = l_Lean_replaceRef(v_declNameId_1063_, v_ref_1081_);
                lean_dec(v_ref_1081_);
                if v_isShared_1094_ == 0 {
                    lean_ctor_set(v___x_1093_, 5, v_ref_1095_);
                    v___x_1097_ = v___x_1093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_fileName_1076_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_fileMap_1077_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_options_1078_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_currRecDepth_1079_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_maxRecDepth_1080_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_ref_1095_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 6, v_currNamespace_1082_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 7, v_openDecls_1083_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 8, v_initHeartbeats_1084_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 9, v_maxHeartbeats_1085_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 10, v_quotContext_1086_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 11, v_currMacroScope_1087_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 12, v_cancelTk_x3f_1089_);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 13, v_inheritedTraceOptions_1091_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1162_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v_diag_1088_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1162_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
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
                if lean_obj_tag(v___x_1098_) == 0 {
                    v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
                    lean_inc(v_a_1099_);
                    lean_dec_ref_known(v___x_1098_, 1);
                    match lean_obj_tag(v_a_1099_) {
                        4 => {
                            v_declName_1100_ = lean_ctor_get(v_a_1099_, 0);
                            lean_inc_n(v_declName_1100_, 3);
                            lean_dec_ref_known(v_a_1099_, 2);
                            v___f_1101_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                            lean_closure_set(v___f_1101_, 0, v_declName_1100_);
                            v___x_1102_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_unfoldLocalDecl___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                1,
                            );
                            lean_closure_set(v___x_1102_, 0, v_declName_1100_);
                            v___x_1103_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_unfoldTarget___boxed as *mut core::ffi::c_void,
                                10,
                                1,
                            );
                            lean_closure_set(v___x_1103_, 0, v_declName_1100_);
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
                            lean_dec_ref(v___x_1097_);
                            return v___x_1104_;
                        }
                        1 => {
                            v_fvarId_1105_ = lean_ctor_get(v_a_1099_, 0);
                            lean_inc(v_fvarId_1105_);
                            v___x_1106_ = l_Lean_FVarId_isLetVar___redArg(
                                v_fvarId_1105_,
                                v___x_1066_,
                                v___y_1071_,
                                v___x_1097_,
                                v___y_1074_,
                            );
                            if lean_obj_tag(v___x_1106_) == 0 {
                                v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
                                lean_inc(v_a_1107_);
                                lean_dec_ref_known(v___x_1106_, 1);
                                lean_inc_ref(v_a_1099_);
                                v___f_1108_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1___boxed as *mut core::ffi::c_void, 11, 1);
                                lean_closure_set(v___f_1108_, 0, v_a_1099_);
                                v___x_1121_ = (lean_unbox(v_a_1107_) as u8);
                                lean_dec(v_a_1107_);
                                if v___x_1121_ == 0 {
                                    lean_dec_ref(v___f_1108_);
                                    v___x_1122_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1);
                                    v___x_1123_ = l_Lean_MessageData_ofExpr(v_a_1099_);
                                    v___x_1124_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_1124_, 0, v___x_1122_);
                                    lean_ctor_set(v___x_1124_, 1, v___x_1123_);
                                    v___x_1125_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3);
                                    v___x_1126_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_1126_, 0, v___x_1124_);
                                    lean_ctor_set(v___x_1126_, 1, v___x_1125_);
                                    v___x_1127_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v___x_1126_, v___y_1071_, v___y_1072_, v___x_1097_, v___y_1074_);
                                    lean_dec_ref(v___x_1097_);
                                    return v___x_1127_;
                                } else {
                                    lean_inc(v_fvarId_1105_);
                                    lean_dec_ref_known(v_a_1099_, 1);
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
                                lean_dec_ref_known(v_a_1099_, 1);
                                lean_dec_ref(v___x_1097_);
                                v_a_1128_ = lean_ctor_get(v___x_1106_, 0);
                                v_isSharedCheck_1135_ = (!lean_is_exclusive(v___x_1106_)) as u8;
                                if v_isSharedCheck_1135_ == 0 {
                                    v___x_1130_ = v___x_1106_;
                                    v_isShared_1131_ = v_isSharedCheck_1135_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_1128_);
                                    lean_dec(v___x_1106_);
                                    v___x_1130_ = lean_box(0);
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
                            if lean_obj_tag(v___x_1136_) == 0 {
                                v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
                                lean_inc(v_a_1137_);
                                lean_dec_ref_known(v___x_1136_, 1);
                                v___x_1138_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1;
                                v___x_1139_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5);
                                v___x_1140_ = l_Lean_MessageData_ofExpr(v_a_1099_);
                                v___x_1141_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1141_, 0, v___x_1139_);
                                lean_ctor_set(v___x_1141_, 1, v___x_1140_);
                                v___x_1142_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7_once), _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7);
                                v___x_1143_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1143_, 0, v___x_1141_);
                                lean_ctor_set(v___x_1143_, 1, v___x_1142_);
                                v___x_1144_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1144_, 0, v___x_1143_);
                                v___x_1145_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_1138_,
                                    v_a_1137_,
                                    v___x_1144_,
                                    v___y_1071_,
                                    v___y_1072_,
                                    v___x_1097_,
                                    v___y_1074_,
                                );
                                lean_dec_ref(v___x_1097_);
                                return v___x_1145_;
                            } else {
                                lean_dec(v_a_1099_);
                                lean_dec_ref(v___x_1097_);
                                v_a_1146_ = lean_ctor_get(v___x_1136_, 0);
                                v_isSharedCheck_1153_ = (!lean_is_exclusive(v___x_1136_)) as u8;
                                if v_isSharedCheck_1153_ == 0 {
                                    v___x_1148_ = v___x_1136_;
                                    v_isShared_1149_ = v_isSharedCheck_1153_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_1146_);
                                    lean_dec(v___x_1136_);
                                    v___x_1148_ = lean_box(0);
                                    v_isShared_1149_ = v_isSharedCheck_1153_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1097_);
                    v_a_1154_ = lean_ctor_get(v___x_1098_, 0);
                    v_isSharedCheck_1161_ = (!lean_is_exclusive(v___x_1098_)) as u8;
                    if v_isSharedCheck_1161_ == 0 {
                        v___x_1156_ = v___x_1098_;
                        v_isShared_1157_ = v_isSharedCheck_1161_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1154_);
                        lean_dec(v___x_1098_);
                        v___x_1156_ = lean_box(0);
                        v_isShared_1157_ = v_isSharedCheck_1161_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_fvarId_1105_);
                v___x_1118_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_zetaDeltaLocalDecl___boxed as *mut core::ffi::c_void,
                    11,
                    1,
                );
                lean_closure_set(v___x_1118_, 0, v_fvarId_1105_);
                v___x_1119_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_zetaDeltaTarget___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                lean_closure_set(v___x_1119_, 0, v_fvarId_1105_);
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
                lean_dec_ref(v___y_1116_);
                return v___x_1120_;
            }
            4 => {
                if v_isShared_1131_ == 0 {
                    v___x_1133_ = v___x_1130_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
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
                    v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
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
                    v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
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
    mut v_declNameId_1164_: *mut LeanObject,
    mut v___x_1165_: *mut LeanObject,
    mut v_loc_1166_: *mut LeanObject,
    mut v___x_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
    mut v___y_1170_: *mut LeanObject,
    mut v___y_1171_: *mut LeanObject,
    mut v___y_1172_: *mut LeanObject,
    mut v___y_1173_: *mut LeanObject,
    mut v___y_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5515__boxed_1177_: u8 = 0;
    let mut v_res_1178_: *mut LeanObject = core::ptr::null_mut();
    v___x_5515__boxed_1177_ = (lean_unbox(v___x_1167_) as u8);
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
    lean_dec(v___y_1175_);
    lean_dec(v___y_1173_);
    lean_dec_ref(v___y_1172_);
    lean_dec(v___y_1171_);
    lean_dec_ref(v___y_1170_);
    lean_dec(v___y_1169_);
    lean_dec_ref(v___y_1168_);
    lean_dec(v_loc_1166_);
    lean_dec(v_declNameId_1164_);
    return v_res_1178_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go(
    mut v_declNameId_1179_: *mut LeanObject,
    mut v_loc_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_a_1182_: *mut LeanObject,
    mut v_a_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    v___x_1190_ = 0;
    v___x_1191_ = lean_box((v___x_1190_) as usize);
    lean_inc(v_declNameId_1179_);
    v___x_1192_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_elabTermForApply___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    lean_closure_set(v___x_1192_, 0, v_declNameId_1179_);
    lean_closure_set(v___x_1192_, 1, v___x_1191_);
    v___x_1193_ = lean_box((v___x_1190_) as usize);
    v___f_1194_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___boxed
            as *mut core::ffi::c_void,
        13,
        4,
    );
    lean_closure_set(v___f_1194_, 0, v_declNameId_1179_);
    lean_closure_set(v___f_1194_, 1, v___x_1192_);
    lean_closure_set(v___f_1194_, 2, v_loc_1180_);
    lean_closure_set(v___f_1194_, 3, v___x_1193_);
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
    mut v_declNameId_1196_: *mut LeanObject,
    mut v_loc_1197_: *mut LeanObject,
    mut v_a_1198_: *mut LeanObject,
    mut v_a_1199_: *mut LeanObject,
    mut v_a_1200_: *mut LeanObject,
    mut v_a_1201_: *mut LeanObject,
    mut v_a_1202_: *mut LeanObject,
    mut v_a_1203_: *mut LeanObject,
    mut v_a_1204_: *mut LeanObject,
    mut v_a_1205_: *mut LeanObject,
    mut v_a_1206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1207_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1205_);
    lean_dec_ref(v_a_1204_);
    lean_dec(v_a_1203_);
    lean_dec_ref(v_a_1202_);
    lean_dec(v_a_1201_);
    lean_dec_ref(v_a_1200_);
    lean_dec(v_a_1199_);
    lean_dec_ref(v_a_1198_);
    return v_res_1207_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0(
    mut v_00_u03b1_1208_: *mut LeanObject,
    mut v_msg_1209_: *mut LeanObject,
    mut v___y_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v_msg_1209_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
    return v___x_1219_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___boxed(
    mut v_00_u03b1_1220_: *mut LeanObject,
    mut v_msg_1221_: *mut LeanObject,
    mut v___y_1222_: *mut LeanObject,
    mut v___y_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1231_: *mut LeanObject = core::ptr::null_mut();
    v_res_1231_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0(v_00_u03b1_1220_, v_msg_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
    lean_dec(v___y_1229_);
    lean_dec_ref(v___y_1228_);
    lean_dec(v___y_1227_);
    lean_dec_ref(v___y_1226_);
    lean_dec(v___y_1225_);
    lean_dec_ref(v___y_1224_);
    lean_dec(v___y_1223_);
    lean_dec_ref(v___y_1222_);
    return v_res_1231_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(
    mut v_loc_1232_: *mut LeanObject,
    mut v_as_1233_: *mut LeanObject,
    mut v_sz_1234_: usize,
    mut v_i_1235_: usize,
    mut v_b_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1246_: u8 = 0;
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: usize = 0;
    let mut v___x_1252_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1246_ = lean_usize_dec_lt(v_i_1235_, v_sz_1234_);
                if v___x_1246_ == 0 {
                    lean_dec(v_loc_1232_);
                    v___x_1247_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1247_, 0, v_b_1236_);
                    return v___x_1247_;
                } else {
                    v_a_1248_ = lean_array_uget_borrowed(v_as_1233_, v_i_1235_);
                    lean_inc(v_loc_1232_);
                    lean_inc(v_a_1248_);
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
                    if lean_obj_tag(v___x_1249_) == 0 {
                        lean_dec_ref_known(v___x_1249_, 1);
                        v___x_1250_ = lean_box(0);
                        v___x_1251_ = 1usize;
                        v___x_1252_ = lean_usize_add(v_i_1235_, v___x_1251_);
                        v_i_1235_ = v___x_1252_;
                        v_b_1236_ = v___x_1250_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_loc_1232_);
                        return v___x_1249_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0___boxed(
    mut v_loc_1254_: *mut LeanObject,
    mut v_as_1255_: *mut LeanObject,
    mut v_sz_1256_: *mut LeanObject,
    mut v_i_1257_: *mut LeanObject,
    mut v_b_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1268_: usize = 0;
    let mut v_i_boxed_1269_: usize = 0;
    let mut v_res_1270_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1268_ = lean_unbox_usize(v_sz_1256_);
    lean_dec(v_sz_1256_);
    v_i_boxed_1269_ = lean_unbox_usize(v_i_1257_);
    lean_dec(v_i_1257_);
    v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(v_loc_1254_, v_as_1255_, v_sz_boxed_1268_, v_i_boxed_1269_, v_b_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
    lean_dec(v___y_1266_);
    lean_dec_ref(v___y_1265_);
    lean_dec(v___y_1264_);
    lean_dec_ref(v___y_1263_);
    lean_dec(v___y_1262_);
    lean_dec_ref(v___y_1261_);
    lean_dec(v___y_1260_);
    lean_dec_ref(v___y_1259_);
    lean_dec_ref(v_as_1255_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalUnfold(
    mut v_stx_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
    mut v_a_1274_: *mut LeanObject,
    mut v_a_1275_: *mut LeanObject,
    mut v_a_1276_: *mut LeanObject,
    mut v_a_1277_: *mut LeanObject,
    mut v_a_1278_: *mut LeanObject,
    mut v_a_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1288_: usize = 0;
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1293_: u8 = 0;
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut v_unused_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1281_ = lean_unsigned_to_nat(2);
                v___x_1282_ = l_Lean_Syntax_getArg(v_stx_1271_, v___x_1281_);
                v_loc_1283_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1282_);
                lean_dec(v___x_1282_);
                v___x_1284_ = lean_unsigned_to_nat(1);
                v___x_1285_ = l_Lean_Syntax_getArg(v_stx_1271_, v___x_1284_);
                v___x_1286_ = l_Lean_Syntax_getArgs(v___x_1285_);
                lean_dec(v___x_1285_);
                v___x_1287_ = lean_box(0);
                v_sz_1288_ = lean_array_size(v___x_1286_);
                v___x_1289_ = 0usize;
                v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(v_loc_1283_, v___x_1286_, v_sz_1288_, v___x_1289_, v___x_1287_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
                lean_dec_ref(v___x_1286_);
                if lean_obj_tag(v___x_1290_) == 0 {
                    v_isSharedCheck_1297_ = (!lean_is_exclusive(v___x_1290_)) as u8;
                    if v_isSharedCheck_1297_ == 0 {
                        v_unused_1298_ = lean_ctor_get(v___x_1290_, 0);
                        lean_dec(v_unused_1298_);
                        v___x_1292_ = v___x_1290_;
                        v_isShared_1293_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1290_);
                        v___x_1292_ = lean_box(0);
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
                    lean_ctor_set(v___x_1292_, 0, v___x_1287_);
                    v___x_1295_ = v___x_1292_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1287_);
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
    mut v_stx_1299_: *mut LeanObject,
    mut v_a_1300_: *mut LeanObject,
    mut v_a_1301_: *mut LeanObject,
    mut v_a_1302_: *mut LeanObject,
    mut v_a_1303_: *mut LeanObject,
    mut v_a_1304_: *mut LeanObject,
    mut v_a_1305_: *mut LeanObject,
    mut v_a_1306_: *mut LeanObject,
    mut v_a_1307_: *mut LeanObject,
    mut v_a_1308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1309_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1307_);
    lean_dec_ref(v_a_1306_);
    lean_dec(v_a_1305_);
    lean_dec_ref(v_a_1304_);
    lean_dec(v_a_1303_);
    lean_dec_ref(v_a_1302_);
    lean_dec(v_a_1301_);
    lean_dec_ref(v_a_1300_);
    lean_dec(v_stx_1299_);
    return v_res_1309_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1()
-> *mut LeanObject {
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    v___x_1326_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1327_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3;
    v___x_1328_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6;
    v___x_1329_ = lean_alloc_closure(
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
    mut v_a_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1332_: *mut LeanObject = core::ptr::null_mut();
    v_res_1332_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1();
    return v_res_1332_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3()
-> *mut LeanObject {
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    v___x_1335_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6;
    v___x_1336_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0;
    v___x_1337_ = l_Lean_addBuiltinDocString(v___x_1335_, v___x_1336_);
    return v___x_1337_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___boxed(
    mut v_a_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1339_: *mut LeanObject = core::ptr::null_mut();
    v_res_1339_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3();
    return v_res_1339_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5()
-> *mut LeanObject {
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    v___x_1366_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6;
    v___x_1367_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6;
    v___x_1368_ = l_Lean_addBuiltinDeclarationRanges(v___x_1366_, v___x_1367_);
    return v___x_1368_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___boxed(
    mut v_a_1369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1370_: *mut LeanObject = core::ptr::null_mut();
    v_res_1370_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5();
    return v_res_1370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Unfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Unfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Unfold(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Unfold(builtin);
}
