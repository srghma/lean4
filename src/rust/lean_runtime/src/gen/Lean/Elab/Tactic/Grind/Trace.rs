// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Trace
// Imports: Lean.Elab.Tactic.Grind.Basic Lean.Elab.Tactic.Grind.Config Lean.Elab.Tactic.Grind.Param Lean.Meta.Tactic.TryThis Lean.Meta.Tactic.Grind.Finish Lean.Meta.Tactic.Grind.CollectParams
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_isNone,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr5, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Grind::Basic::{
    initialize_Lean_Elab_Tactic_Grind_Basic, l_Lean_Elab_Tactic_Grind_getMainGoal___redArg,
    l_Lean_Elab_Tactic_Grind_grindTacElabAttribute, l_Lean_Elab_Tactic_Grind_liftGrindM___redArg,
    l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg,
    runtime_initialize_Lean_Elab_Tactic_Grind_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Config::{
    initialize_Lean_Elab_Tactic_Grind_Config, l_Lean_Elab_Tactic_Grind_withConfigItems___redArg,
    runtime_initialize_Lean_Elab_Tactic_Grind_Config,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Param::{
    initialize_Lean_Elab_Tactic_Grind_Param, l_Lean_Elab_Tactic_Grind_withParams___redArg,
    runtime_initialize_Lean_Elab_Tactic_Grind_Param,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_nil, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Action::{
    l_Lean_Meta_Grind_Action_checkSeqAt, l_Lean_Meta_Grind_Action_mkGrindSeq,
    l_Lean_Meta_Grind_Action_run,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::CollectParams::{
    initialize_Lean_Meta_Tactic_Grind_CollectParams, l_Lean_Meta_Grind_mkFinishTactic,
    runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Finish::{
    initialize_Lean_Meta_Tactic_Grind_Finish, l_Lean_Meta_Grind_Action_mkFinish,
    runtime_initialize_Lean_Meta_Tactic_Grind_Finish,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    l_Lean_Meta_Grind_Result_toMessageData, l_Lean_Meta_Grind_mkResult,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_saveState___redArg;
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addSuggestion,
    l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [103, 114, 105, 110, 100, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__2_value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [84, 114, 121, 32, 116, 104, 101, 115, 101, 58, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [96, 102, 105, 110, 105, 115, 104, 63, 96, 32, 102, 97, 105, 108, 101, 100, 10, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 102, 105, 110, 105, 115, 104, 63, 96, 32, 102, 97, 105, 108, 101, 100, 44, 32, 98, 117, 116, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 103, 111, 97, 108, 32, 105, 115, 32, 110, 111, 116, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__4_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [102, 105, 110, 105, 115, 104, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__4_value) as *mut LeanObject,10423707108080707712 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__6_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value) as *mut LeanObject,4907018543776028915 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__7_value) as *mut LeanObject,174571072631544762 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__8_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,5180440899797302363 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0_value) as *mut LeanObject,7611094341194159974 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__3_value) as *mut LeanObject,5833523922800478868 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2_value) as *mut LeanObject,5059995712231706049 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3_value) as *mut LeanObject,2252997831174394975 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 70, 105, 110, 105, 115, 104, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__14_value) as *mut LeanObject,4823722285856129054 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__15_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(
    mut v_x_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
    mut v_a_738_: *mut LeanObject,
    mut v_a_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ctx_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sctx_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sym_748_: u8 = 0;
    let mut v_simp_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simpMethods_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anchorRefs_x3f_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cheapCases_752_: u8 = 0;
    let mut v_reportMVarIssue_753_: u8 = 0;
    let mut v_splitSource_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematchDiagSource_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_symPrios_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_758_: u8 = 0;
    let mut v_ematchDiag_759_: u8 = 0;
    let mut v_markInstances_760_: u8 = 0;
    let mut v_lax_761_: u8 = 0;
    let mut v_suggestions_762_: u8 = 0;
    let mut v_locals_763_: u8 = 0;
    let mut v_splits_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gen_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_genLocal_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instances_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matchEqs_769_: u8 = 0;
    let mut v_splitMatch_770_: u8 = 0;
    let mut v_splitIte_771_: u8 = 0;
    let mut v_splitIndPred_772_: u8 = 0;
    let mut v_splitImp_773_: u8 = 0;
    let mut v_canonHeartbeats_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_775_: u8 = 0;
    let mut v_extAll_776_: u8 = 0;
    let mut v_etaStruct_777_: u8 = 0;
    let mut v_funext_778_: u8 = 0;
    let mut v_lookahead_779_: u8 = 0;
    let mut v_verbose_780_: u8 = 0;
    let mut v_clean_781_: u8 = 0;
    let mut v_qlia_782_: u8 = 0;
    let mut v_mbtc_783_: u8 = 0;
    let mut v_zetaDelta_784_: u8 = 0;
    let mut v_zeta_785_: u8 = 0;
    let mut v_ring_786_: u8 = 0;
    let mut v_ringSteps_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringMaxDegree_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linarith_789_: u8 = 0;
    let mut v_lia_790_: u8 = 0;
    let mut v_ac_791_: u8 = 0;
    let mut v_acSteps_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exp_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abstractProof_794_: u8 = 0;
    let mut v_inj_795_: u8 = 0;
    let mut v_order_796_: u8 = 0;
    let mut v_min_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_detailed_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_useSorry_799_: u8 = 0;
    let mut v_revert_800_: u8 = 0;
    let mut v_funCC_801_: u8 = 0;
    let mut v_reducible_802_: u8 = 0;
    let mut v_maxSuggestions_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: u8 = 0;
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v_ctx_742_ = lean_ctor_get(v_a_733_, 1);
    v_config_743_ = lean_ctor_get(v_ctx_742_, 2);
    v_toContext_744_ = lean_ctor_get(v_a_733_, 0);
    v_sctx_745_ = lean_ctor_get(v_a_733_, 2);
    v_methods_746_ = lean_ctor_get(v_a_733_, 3);
    v_params_747_ = lean_ctor_get(v_a_733_, 4);
    v_sym_748_ = lean_ctor_get_uint8(
        v_a_733_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
    );
    v_simp_749_ = lean_ctor_get(v_ctx_742_, 0);
    v_simpMethods_750_ = lean_ctor_get(v_ctx_742_, 1);
    v_anchorRefs_x3f_751_ = lean_ctor_get(v_ctx_742_, 3);
    v_cheapCases_752_ = lean_ctor_get_uint8(
        v_ctx_742_,
        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
    );
    v_reportMVarIssue_753_ = lean_ctor_get_uint8(
        v_ctx_742_,
        (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
    );
    v_splitSource_754_ = lean_ctor_get(v_ctx_742_, 4);
    v_ematchDiagSource_755_ = lean_ctor_get(v_ctx_742_, 5);
    v_symPrios_756_ = lean_ctor_get(v_ctx_742_, 6);
    v_extensions_757_ = lean_ctor_get(v_ctx_742_, 7);
    v_debug_758_ = lean_ctor_get_uint8(
        v_ctx_742_,
        (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
    );
    v_ematchDiag_759_ = lean_ctor_get_uint8(
        v_ctx_742_,
        (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
    );
    v_markInstances_760_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
    );
    v_lax_761_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 2) as u32,
    );
    v_suggestions_762_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 3) as u32,
    );
    v_locals_763_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 4) as u32,
    );
    v_splits_764_ = lean_ctor_get(v_config_743_, 0);
    v_ematch_765_ = lean_ctor_get(v_config_743_, 1);
    v_gen_766_ = lean_ctor_get(v_config_743_, 2);
    v_genLocal_767_ = lean_ctor_get(v_config_743_, 3);
    v_instances_768_ = lean_ctor_get(v_config_743_, 4);
    v_matchEqs_769_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 5) as u32,
    );
    v_splitMatch_770_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 6) as u32,
    );
    v_splitIte_771_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 7) as u32,
    );
    v_splitIndPred_772_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 8) as u32,
    );
    v_splitImp_773_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 9) as u32,
    );
    v_canonHeartbeats_774_ = lean_ctor_get(v_config_743_, 5);
    v_ext_775_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 10) as u32,
    );
    v_extAll_776_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 11) as u32,
    );
    v_etaStruct_777_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 12) as u32,
    );
    v_funext_778_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 13) as u32,
    );
    v_lookahead_779_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 14) as u32,
    );
    v_verbose_780_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 15) as u32,
    );
    v_clean_781_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 16) as u32,
    );
    v_qlia_782_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 17) as u32,
    );
    v_mbtc_783_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 18) as u32,
    );
    v_zetaDelta_784_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 19) as u32,
    );
    v_zeta_785_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 20) as u32,
    );
    v_ring_786_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 21) as u32,
    );
    v_ringSteps_787_ = lean_ctor_get(v_config_743_, 6);
    v_ringMaxDegree_788_ = lean_ctor_get(v_config_743_, 7);
    v_linarith_789_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 22) as u32,
    );
    v_lia_790_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 23) as u32,
    );
    v_ac_791_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 24) as u32,
    );
    v_acSteps_792_ = lean_ctor_get(v_config_743_, 8);
    v_exp_793_ = lean_ctor_get(v_config_743_, 9);
    v_abstractProof_794_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 25) as u32,
    );
    v_inj_795_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 26) as u32,
    );
    v_order_796_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 27) as u32,
    );
    v_min_797_ = lean_ctor_get(v_config_743_, 10);
    v_detailed_798_ = lean_ctor_get(v_config_743_, 11);
    v_useSorry_799_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 28) as u32,
    );
    v_revert_800_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 29) as u32,
    );
    v_funCC_801_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 30) as u32,
    );
    v_reducible_802_ = lean_ctor_get_uint8(
        v_config_743_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 31) as u32,
    );
    v_maxSuggestions_803_ = lean_ctor_get(v_config_743_, 12);
    v___x_804_ = 1;
    lean_inc(v_maxSuggestions_803_);
    lean_inc(v_detailed_798_);
    lean_inc(v_min_797_);
    lean_inc(v_exp_793_);
    lean_inc(v_acSteps_792_);
    lean_inc(v_ringMaxDegree_788_);
    lean_inc(v_ringSteps_787_);
    lean_inc(v_canonHeartbeats_774_);
    lean_inc(v_instances_768_);
    lean_inc(v_genLocal_767_);
    lean_inc(v_gen_766_);
    lean_inc(v_ematch_765_);
    lean_inc(v_splits_764_);
    v___x_805_ = lean_alloc_ctor(0, 13, (32) as u32);
    lean_ctor_set(v___x_805_, 0, v_splits_764_);
    lean_ctor_set(v___x_805_, 1, v_ematch_765_);
    lean_ctor_set(v___x_805_, 2, v_gen_766_);
    lean_ctor_set(v___x_805_, 3, v_genLocal_767_);
    lean_ctor_set(v___x_805_, 4, v_instances_768_);
    lean_ctor_set(v___x_805_, 5, v_canonHeartbeats_774_);
    lean_ctor_set(v___x_805_, 6, v_ringSteps_787_);
    lean_ctor_set(v___x_805_, 7, v_ringMaxDegree_788_);
    lean_ctor_set(v___x_805_, 8, v_acSteps_792_);
    lean_ctor_set(v___x_805_, 9, v_exp_793_);
    lean_ctor_set(v___x_805_, 10, v_min_797_);
    lean_ctor_set(v___x_805_, 11, v_detailed_798_);
    lean_ctor_set(v___x_805_, 12, v_maxSuggestions_803_);
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
        v___x_804_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
        v_markInstances_760_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 2) as u32,
        v_lax_761_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 3) as u32,
        v_suggestions_762_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 4) as u32,
        v_locals_763_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 5) as u32,
        v_matchEqs_769_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 6) as u32,
        v_splitMatch_770_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 7) as u32,
        v_splitIte_771_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 8) as u32,
        v_splitIndPred_772_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 9) as u32,
        v_splitImp_773_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 10) as u32,
        v_ext_775_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 11) as u32,
        v_extAll_776_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 12) as u32,
        v_etaStruct_777_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 13) as u32,
        v_funext_778_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 14) as u32,
        v_lookahead_779_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 15) as u32,
        v_verbose_780_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 16) as u32,
        v_clean_781_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 17) as u32,
        v_qlia_782_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 18) as u32,
        v_mbtc_783_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 19) as u32,
        v_zetaDelta_784_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 20) as u32,
        v_zeta_785_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 21) as u32,
        v_ring_786_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 22) as u32,
        v_linarith_789_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 23) as u32,
        v_lia_790_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 24) as u32,
        v_ac_791_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 25) as u32,
        v_abstractProof_794_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 26) as u32,
        v_inj_795_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 27) as u32,
        v_order_796_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 28) as u32,
        v_useSorry_799_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 29) as u32,
        v_revert_800_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 30) as u32,
        v_funCC_801_,
    );
    lean_ctor_set_uint8(
        v___x_805_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 31) as u32,
        v_reducible_802_,
    );
    lean_inc_ref(v_extensions_757_);
    lean_inc_ref(v_symPrios_756_);
    lean_inc(v_ematchDiagSource_755_);
    lean_inc(v_splitSource_754_);
    lean_inc(v_anchorRefs_x3f_751_);
    lean_inc_ref(v_simpMethods_750_);
    lean_inc_ref(v_simp_749_);
    v___x_806_ = lean_alloc_ctor(0, 8, (4) as u32);
    lean_ctor_set(v___x_806_, 0, v_simp_749_);
    lean_ctor_set(v___x_806_, 1, v_simpMethods_750_);
    lean_ctor_set(v___x_806_, 2, v___x_805_);
    lean_ctor_set(v___x_806_, 3, v_anchorRefs_x3f_751_);
    lean_ctor_set(v___x_806_, 4, v_splitSource_754_);
    lean_ctor_set(v___x_806_, 5, v_ematchDiagSource_755_);
    lean_ctor_set(v___x_806_, 6, v_symPrios_756_);
    lean_ctor_set(v___x_806_, 7, v_extensions_757_);
    lean_ctor_set_uint8(
        v___x_806_,
        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
        v_cheapCases_752_,
    );
    lean_ctor_set_uint8(
        v___x_806_,
        (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
        v_reportMVarIssue_753_,
    );
    lean_ctor_set_uint8(
        v___x_806_,
        (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
        v_debug_758_,
    );
    lean_ctor_set_uint8(
        v___x_806_,
        (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
        v_ematchDiag_759_,
    );
    lean_inc_ref(v_params_747_);
    lean_inc_ref(v_methods_746_);
    lean_inc_ref(v_sctx_745_);
    lean_inc_ref(v_toContext_744_);
    v___x_807_ = lean_alloc_ctor(0, 5, (1) as u32);
    lean_ctor_set(v___x_807_, 0, v_toContext_744_);
    lean_ctor_set(v___x_807_, 1, v___x_806_);
    lean_ctor_set(v___x_807_, 2, v_sctx_745_);
    lean_ctor_set(v___x_807_, 3, v_methods_746_);
    lean_ctor_set(v___x_807_, 4, v_params_747_);
    lean_ctor_set_uint8(
        v___x_807_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v_sym_748_,
    );
    lean_inc(v_a_740_);
    lean_inc_ref(v_a_739_);
    lean_inc(v_a_738_);
    lean_inc_ref(v_a_737_);
    lean_inc(v_a_736_);
    lean_inc_ref(v_a_735_);
    lean_inc(v_a_734_);
    v___x_808_ = lean_apply_9(
        v_x_732_,
        v___x_807_,
        v_a_734_,
        v_a_735_,
        v_a_736_,
        v_a_737_,
        v_a_738_,
        v_a_739_,
        v_a_740_,
        lean_box(0),
    );
    return v___x_808_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg___boxed(
    mut v_x_809_: *mut LeanObject,
    mut v_a_810_: *mut LeanObject,
    mut v_a_811_: *mut LeanObject,
    mut v_a_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_a_814_: *mut LeanObject,
    mut v_a_815_: *mut LeanObject,
    mut v_a_816_: *mut LeanObject,
    mut v_a_817_: *mut LeanObject,
    mut v_a_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_819_: *mut LeanObject = core::ptr::null_mut();
    v_res_819_ =
        l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(
            v_x_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_,
            v_a_817_,
        );
    lean_dec(v_a_817_);
    lean_dec_ref(v_a_816_);
    lean_dec(v_a_815_);
    lean_dec_ref(v_a_814_);
    lean_dec(v_a_813_);
    lean_dec_ref(v_a_812_);
    lean_dec(v_a_811_);
    lean_dec_ref(v_a_810_);
    return v_res_819_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(
    mut v_00_u03b1_820_: *mut LeanObject,
    mut v_x_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
    mut v_a_823_: *mut LeanObject,
    mut v_a_824_: *mut LeanObject,
    mut v_a_825_: *mut LeanObject,
    mut v_a_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
    mut v_a_828_: *mut LeanObject,
    mut v_a_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v___x_831_ =
        l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(
            v_x_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_,
            v_a_829_,
        );
    return v___x_831_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___boxed(
    mut v_00_u03b1_832_: *mut LeanObject,
    mut v_x_833_: *mut LeanObject,
    mut v_a_834_: *mut LeanObject,
    mut v_a_835_: *mut LeanObject,
    mut v_a_836_: *mut LeanObject,
    mut v_a_837_: *mut LeanObject,
    mut v_a_838_: *mut LeanObject,
    mut v_a_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_843_: *mut LeanObject = core::ptr::null_mut();
    v_res_843_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing(
        v_00_u03b1_832_,
        v_x_833_,
        v_a_834_,
        v_a_835_,
        v_a_836_,
        v_a_837_,
        v_a_838_,
        v_a_839_,
        v_a_840_,
        v_a_841_,
    );
    lean_dec(v_a_841_);
    lean_dec_ref(v_a_840_);
    lean_dec(v_a_839_);
    lean_dec_ref(v_a_838_);
    lean_dec(v_a_837_);
    lean_dec_ref(v_a_836_);
    lean_dec(v_a_835_);
    lean_dec_ref(v_a_834_);
    return v_res_843_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    v___x_844_ = lean_box(0);
    v___x_845_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_846_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_846_, 0, v___x_845_);
    lean_ctor_set(v___x_846_, 1, v___x_844_);
    return v___x_846_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___closed__0);
    v___x_849_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_849_, 0, v___x_848_);
    return v___x_849_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg___boxed(
    mut v___y_850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_851_: *mut LeanObject = core::ptr::null_mut();
    v_res_851_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
    return v_res_851_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(
    mut v_00_u03b1_852_: *mut LeanObject,
    mut v___y_853_: *mut LeanObject,
    mut v___y_854_: *mut LeanObject,
    mut v___y_855_: *mut LeanObject,
    mut v___y_856_: *mut LeanObject,
    mut v___y_857_: *mut LeanObject,
    mut v___y_858_: *mut LeanObject,
    mut v___y_859_: *mut LeanObject,
    mut v___y_860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    v___x_862_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
    return v___x_862_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___boxed(
    mut v_00_u03b1_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
    mut v___y_865_: *mut LeanObject,
    mut v___y_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
    mut v___y_868_: *mut LeanObject,
    mut v___y_869_: *mut LeanObject,
    mut v___y_870_: *mut LeanObject,
    mut v___y_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_873_: *mut LeanObject = core::ptr::null_mut();
    v_res_873_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0(v_00_u03b1_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
    lean_dec(v___y_871_);
    lean_dec_ref(v___y_870_);
    lean_dec(v___y_869_);
    lean_dec_ref(v___y_868_);
    lean_dec(v___y_867_);
    lean_dec_ref(v___y_866_);
    lean_dec(v___y_865_);
    lean_dec_ref(v___y_864_);
    return v_res_873_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(
    mut v_msgData_874_: *mut LeanObject,
    mut v___y_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
    mut v___y_877_: *mut LeanObject,
    mut v___y_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_880_ = lean_st_ref_get(v___y_878_);
    v_env_881_ = lean_ctor_get(v___x_880_, 0);
    lean_inc_ref(v_env_881_);
    lean_dec(v___x_880_);
    v___x_882_ = lean_st_ref_get(v___y_876_);
    v_mctx_883_ = lean_ctor_get(v___x_882_, 0);
    lean_inc_ref(v_mctx_883_);
    lean_dec(v___x_882_);
    v_lctx_884_ = lean_ctor_get(v___y_875_, 2);
    v_options_885_ = lean_ctor_get(v___y_877_, 2);
    lean_inc_ref(v_options_885_);
    lean_inc_ref(v_lctx_884_);
    v___x_886_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_886_, 0, v_env_881_);
    lean_ctor_set(v___x_886_, 1, v_mctx_883_);
    lean_ctor_set(v___x_886_, 2, v_lctx_884_);
    lean_ctor_set(v___x_886_, 3, v_options_885_);
    v___x_887_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_887_, 0, v___x_886_);
    lean_ctor_set(v___x_887_, 1, v_msgData_874_);
    v___x_888_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_888_, 0, v___x_887_);
    return v___x_888_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2___boxed(
    mut v_msgData_889_: *mut LeanObject,
    mut v___y_890_: *mut LeanObject,
    mut v___y_891_: *mut LeanObject,
    mut v___y_892_: *mut LeanObject,
    mut v___y_893_: *mut LeanObject,
    mut v___y_894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_895_: *mut LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msgData_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
    lean_dec(v___y_893_);
    lean_dec_ref(v___y_892_);
    lean_dec(v___y_891_);
    lean_dec_ref(v___y_890_);
    return v_res_895_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(
    mut v_msg_896_: *mut LeanObject,
    mut v___y_897_: *mut LeanObject,
    mut v___y_898_: *mut LeanObject,
    mut v___y_899_: *mut LeanObject,
    mut v___y_900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_907_: u8 = 0;
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_902_ = lean_ctor_get(v___y_899_, 5);
                v___x_903_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2_spec__2(v_msg_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
                v_a_904_ = lean_ctor_get(v___x_903_, 0);
                v_isSharedCheck_912_ = (!lean_is_exclusive(v___x_903_)) as u8;
                if v_isSharedCheck_912_ == 0 {
                    v___x_906_ = v___x_903_;
                    v_isShared_907_ = v_isSharedCheck_912_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_904_);
                    lean_dec(v___x_903_);
                    v___x_906_ = lean_box(0);
                    v_isShared_907_ = v_isSharedCheck_912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_902_);
                v___x_908_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_908_, 0, v_ref_902_);
                lean_ctor_set(v___x_908_, 1, v_a_904_);
                if v_isShared_907_ == 0 {
                    lean_ctor_set_tag(v___x_906_, 1);
                    lean_ctor_set(v___x_906_, 0, v___x_908_);
                    v___x_910_ = v___x_906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
                    v___x_910_ = v_reuseFailAlloc_911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg___boxed(
    mut v_msg_913_: *mut LeanObject,
    mut v___y_914_: *mut LeanObject,
    mut v___y_915_: *mut LeanObject,
    mut v___y_916_: *mut LeanObject,
    mut v___y_917_: *mut LeanObject,
    mut v___y_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_919_: *mut LeanObject = core::ptr::null_mut();
    v_res_919_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(v_msg_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
    lean_dec(v___y_917_);
    lean_dec_ref(v___y_916_);
    lean_dec(v___y_915_);
    lean_dec_ref(v___y_914_);
    return v_res_919_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__5;
    v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
    return v___x_928_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8()
-> *mut LeanObject {
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    v___x_930_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__7;
    v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
    return v___x_931_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(
    mut v_a_932_: *mut LeanObject,
    mut v_a_933_: *mut LeanObject,
    mut v___x_934_: *mut LeanObject,
    mut v___x_935_: *mut LeanObject,
    mut v___x_936_: *mut LeanObject,
    mut v___x_937_: *mut LeanObject,
    mut v_stx_938_: *mut LeanObject,
    mut v___x_939_: u8,
    mut v_params_940_: *mut LeanObject,
    mut v___y_941_: *mut LeanObject,
    mut v___y_942_: *mut LeanObject,
    mut v___y_943_: *mut LeanObject,
    mut v___y_944_: *mut LeanObject,
    mut v___y_945_: *mut LeanObject,
    mut v___y_946_: *mut LeanObject,
    mut v___y_947_: *mut LeanObject,
    mut v___y_948_: *mut LeanObject,
    mut v___y_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seq_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_958_: u8 = 0;
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: u8 = 0;
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_980_: u8 = 0;
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_985_: u8 = 0;
    let mut v_unused_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_994_: u8 = 0;
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: u8 = 0;
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1013_: u8 = 0;
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1018_: u8 = 0;
    let mut v_unused_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1023_: u8 = 0;
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1027_: u8 = 0;
    let mut v_reuseFailAlloc_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1032_: u8 = 0;
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1036_: u8 = 0;
    let mut v_isSharedCheck_1037_: u8 = 0;
    let mut v_gs_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1041_: u8 = 0;
    let mut v_head_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1045_: u8 = 0;
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1063_: u8 = 0;
    let mut v_reuseFailAlloc_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1068_: u8 = 0;
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1072_: u8 = 0;
    let mut v_a_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1076_: u8 = 0;
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_reuseFailAlloc_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1082_: u8 = 0;
    let mut v_unused_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1086_: u8 = 0;
    let mut v_a_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1090_: u8 = 0;
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut v_a_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_951_ =
                    l_Lean_Meta_Grind_saveState___redArg(v___y_943_, v___y_947_, v___y_949_);
                if lean_obj_tag(v___x_951_) == 0 {
                    v_a_952_ = lean_ctor_get(v___x_951_, 0);
                    lean_inc(v_a_952_);
                    lean_dec_ref_known(v___x_951_, 1);
                    lean_inc_ref(v_a_932_);
                    v___x_953_ = l_Lean_Meta_Grind_Action_run(
                        v_a_932_, v_a_933_, v___y_941_, v___y_942_, v___y_943_, v___y_944_,
                        v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_,
                    );
                    if lean_obj_tag(v___x_953_) == 0 {
                        v_a_954_ = lean_ctor_get(v___x_953_, 0);
                        lean_inc(v_a_954_);
                        lean_dec_ref_known(v___x_953_, 1);
                        if lean_obj_tag(v_a_954_) == 0 {
                            v_seq_955_ = lean_ctor_get(v_a_954_, 0);
                            v_isSharedCheck_1037_ = (!lean_is_exclusive(v_a_954_)) as u8;
                            if v_isSharedCheck_1037_ == 0 {
                                v___x_957_ = v_a_954_;
                                v_isShared_958_ = v_isSharedCheck_1037_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_seq_955_);
                                lean_dec(v_a_954_);
                                v___x_957_ = lean_box(0);
                                v_isShared_958_ = v_isSharedCheck_1037_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_952_);
                            lean_dec(v_stx_938_);
                            lean_dec_ref(v___x_937_);
                            lean_dec_ref(v___x_936_);
                            lean_dec_ref(v___x_935_);
                            lean_dec_ref(v___x_934_);
                            lean_dec_ref(v_a_932_);
                            v_gs_1038_ = lean_ctor_get(v_a_954_, 0);
                            v_isSharedCheck_1086_ = (!lean_is_exclusive(v_a_954_)) as u8;
                            if v_isSharedCheck_1086_ == 0 {
                                v___x_1040_ = v_a_954_;
                                v_isShared_1041_ = v_isSharedCheck_1086_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_gs_1038_);
                                lean_dec(v_a_954_);
                                v___x_1040_ = lean_box(0);
                                v_isShared_1041_ = v_isSharedCheck_1086_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_952_);
                        lean_dec(v_stx_938_);
                        lean_dec_ref(v___x_937_);
                        lean_dec_ref(v___x_936_);
                        lean_dec_ref(v___x_935_);
                        lean_dec_ref(v___x_934_);
                        lean_dec_ref(v_a_932_);
                        v_a_1087_ = lean_ctor_get(v___x_953_, 0);
                        v_isSharedCheck_1094_ = (!lean_is_exclusive(v___x_953_)) as u8;
                        if v_isSharedCheck_1094_ == 0 {
                            v___x_1089_ = v___x_953_;
                            v_isShared_1090_ = v_isSharedCheck_1094_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_1087_);
                            lean_dec(v___x_953_);
                            v___x_1089_ = lean_box(0);
                            v_isShared_1090_ = v_isSharedCheck_1094_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_stx_938_);
                    lean_dec_ref(v___x_937_);
                    lean_dec_ref(v___x_936_);
                    lean_dec_ref(v___x_935_);
                    lean_dec_ref(v___x_934_);
                    lean_dec_ref(v_a_933_);
                    lean_dec_ref(v_a_932_);
                    v_a_1095_ = lean_ctor_get(v___x_951_, 0);
                    v_isSharedCheck_1102_ = (!lean_is_exclusive(v___x_951_)) as u8;
                    if v_isSharedCheck_1102_ == 0 {
                        v___x_1097_ = v___x_951_;
                        v_isShared_1098_ = v_isSharedCheck_1102_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_1095_);
                        lean_dec(v___x_951_);
                        v___x_1097_ = lean_box(0);
                        v_isShared_1098_ = v_isSharedCheck_1102_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_seq_955_);
                v___x_959_ = l_Lean_Meta_Grind_mkFinishTactic(v_seq_955_, v___y_948_, v___y_949_);
                if lean_obj_tag(v___x_959_) == 0 {
                    v_a_960_ = lean_ctor_get(v___x_959_, 0);
                    lean_inc(v_a_960_);
                    lean_dec_ref_known(v___x_959_, 1);
                    if v_isShared_958_ == 0 {
                        lean_ctor_set_tag(v___x_957_, 1);
                        lean_ctor_set(v___x_957_, 0, v_a_952_);
                        v___x_962_ = v___x_957_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_952_);
                        v___x_962_ = v_reuseFailAlloc_1028_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_957_);
                    lean_dec(v_seq_955_);
                    lean_dec(v_a_952_);
                    lean_dec(v_stx_938_);
                    lean_dec_ref(v___x_937_);
                    lean_dec_ref(v___x_936_);
                    lean_dec_ref(v___x_935_);
                    lean_dec_ref(v___x_934_);
                    lean_dec_ref(v_a_932_);
                    v_a_1029_ = lean_ctor_get(v___x_959_, 0);
                    v_isSharedCheck_1036_ = (!lean_is_exclusive(v___x_959_)) as u8;
                    if v_isSharedCheck_1036_ == 0 {
                        v___x_1031_ = v___x_959_;
                        v_isShared_1032_ = v_isSharedCheck_1036_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1029_);
                        lean_dec(v___x_959_);
                        v___x_1031_ = lean_box(0);
                        v_isShared_1032_ = v_isSharedCheck_1036_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v___x_963_ = lean_box(0);
                lean_inc(v_a_960_);
                v___x_964_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_964_, 0, v_a_960_);
                lean_ctor_set(v___x_964_, 1, v___x_963_);
                v___x_965_ = l_Lean_Meta_Grind_Action_checkSeqAt(
                    v___x_962_, v_a_932_, v___x_964_, v___y_941_, v___y_942_, v___y_943_,
                    v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_,
                );
                if lean_obj_tag(v___x_965_) == 0 {
                    v_a_966_ = lean_ctor_get(v___x_965_, 0);
                    lean_inc(v_a_966_);
                    lean_dec_ref_known(v___x_965_, 1);
                    v___x_967_ = l_Lean_Meta_Grind_Action_mkGrindSeq(v_seq_955_);
                    v___x_968_ = (lean_unbox(v_a_966_) as u8);
                    lean_dec(v_a_966_);
                    if v___x_968_ == 0 {
                        lean_dec(v_a_960_);
                        v___x_969_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0;
                        v___x_970_ = l_Lean_Name_mkStr5(
                            v___x_934_, v___x_935_, v___x_936_, v___x_937_, v___x_969_,
                        );
                        v___x_971_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_971_, 0, v___x_970_);
                        lean_ctor_set(v___x_971_, 1, v___x_967_);
                        v___x_972_ = lean_box(0);
                        v___x_973_ = lean_alloc_ctor(0, 6, (0) as u32);
                        lean_ctor_set(v___x_973_, 0, v___x_971_);
                        lean_ctor_set(v___x_973_, 1, v___x_972_);
                        lean_ctor_set(v___x_973_, 2, v___x_972_);
                        lean_ctor_set(v___x_973_, 3, v___x_972_);
                        lean_ctor_set(v___x_973_, 4, v___x_972_);
                        lean_ctor_set(v___x_973_, 5, v___x_972_);
                        v___x_974_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__1;
                        v___x_975_ = 4;
                        v___x_976_ = l_Lean_MessageData_nil;
                        v___x_977_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                            v_stx_938_, v___x_973_, v___x_972_, v___x_974_, v___x_972_, v___x_975_,
                            v___x_976_, v___y_948_, v___y_949_,
                        );
                        if lean_obj_tag(v___x_977_) == 0 {
                            v_isSharedCheck_985_ = (!lean_is_exclusive(v___x_977_)) as u8;
                            if v_isSharedCheck_985_ == 0 {
                                v_unused_986_ = lean_ctor_get(v___x_977_, 0);
                                lean_dec(v_unused_986_);
                                v___x_979_ = v___x_977_;
                                v_isShared_980_ = v_isSharedCheck_985_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_977_);
                                v___x_979_ = lean_box(0);
                                v_isShared_980_ = v_isSharedCheck_985_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_987_ = lean_ctor_get(v___x_977_, 0);
                            v_isSharedCheck_994_ = (!lean_is_exclusive(v___x_977_)) as u8;
                            if v_isSharedCheck_994_ == 0 {
                                v___x_989_ = v___x_977_;
                                v_isShared_990_ = v_isSharedCheck_994_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_987_);
                                lean_dec(v___x_977_);
                                v___x_989_ = lean_box(0);
                                v_isShared_990_ = v_isSharedCheck_994_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_995_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__0;
                        v___x_996_ = l_Lean_Name_mkStr5(
                            v___x_934_, v___x_935_, v___x_936_, v___x_937_, v___x_995_,
                        );
                        v___x_997_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_997_, 0, v___x_996_);
                        lean_ctor_set(v___x_997_, 1, v___x_967_);
                        v___x_998_ = lean_box(0);
                        v___x_999_ = lean_alloc_ctor(0, 6, (0) as u32);
                        lean_ctor_set(v___x_999_, 0, v___x_997_);
                        lean_ctor_set(v___x_999_, 1, v___x_998_);
                        lean_ctor_set(v___x_999_, 2, v___x_998_);
                        lean_ctor_set(v___x_999_, 3, v___x_998_);
                        lean_ctor_set(v___x_999_, 4, v___x_998_);
                        lean_ctor_set(v___x_999_, 5, v___x_998_);
                        v___x_1000_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__3;
                        v___x_1001_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1001_, 0, v___x_1000_);
                        lean_ctor_set(v___x_1001_, 1, v_a_960_);
                        v___x_1002_ = lean_alloc_ctor(0, 6, (0) as u32);
                        lean_ctor_set(v___x_1002_, 0, v___x_1001_);
                        lean_ctor_set(v___x_1002_, 1, v___x_998_);
                        lean_ctor_set(v___x_1002_, 2, v___x_998_);
                        lean_ctor_set(v___x_1002_, 3, v___x_998_);
                        lean_ctor_set(v___x_1002_, 4, v___x_998_);
                        lean_ctor_set(v___x_1002_, 5, v___x_998_);
                        v___x_1003_ = lean_unsigned_to_nat(2);
                        v___x_1004_ = lean_mk_empty_array_with_capacity(v___x_1003_);
                        v___x_1005_ = lean_array_push(v___x_1004_, v___x_999_);
                        v___x_1006_ = lean_array_push(v___x_1005_, v___x_1002_);
                        v___x_1007_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__4;
                        v___x_1008_ = 4;
                        v___x_1009_ = l_Lean_MessageData_nil;
                        v___x_1010_ = l_Lean_Meta_Tactic_TryThis_addSuggestions___redArg(
                            v_stx_938_,
                            v___x_1006_,
                            v___x_998_,
                            v___x_1007_,
                            v___x_998_,
                            v___x_1008_,
                            v___x_1009_,
                            v___y_948_,
                            v___y_949_,
                        );
                        if lean_obj_tag(v___x_1010_) == 0 {
                            v_isSharedCheck_1018_ = (!lean_is_exclusive(v___x_1010_)) as u8;
                            if v_isSharedCheck_1018_ == 0 {
                                v_unused_1019_ = lean_ctor_get(v___x_1010_, 0);
                                lean_dec(v_unused_1019_);
                                v___x_1012_ = v___x_1010_;
                                v_isShared_1013_ = v_isSharedCheck_1018_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_1010_);
                                v___x_1012_ = lean_box(0);
                                v_isShared_1013_ = v_isSharedCheck_1018_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_1020_ = lean_ctor_get(v___x_1010_, 0);
                            v_isSharedCheck_1027_ = (!lean_is_exclusive(v___x_1010_)) as u8;
                            if v_isSharedCheck_1027_ == 0 {
                                v___x_1022_ = v___x_1010_;
                                v_isShared_1023_ = v_isSharedCheck_1027_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_1020_);
                                lean_dec(v___x_1010_);
                                v___x_1022_ = lean_box(0);
                                v_isShared_1023_ = v_isSharedCheck_1027_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_960_);
                    lean_dec(v_seq_955_);
                    lean_dec(v_stx_938_);
                    lean_dec_ref(v___x_937_);
                    lean_dec_ref(v___x_936_);
                    lean_dec_ref(v___x_935_);
                    lean_dec_ref(v___x_934_);
                    return v___x_965_;
                }
            }
            3 => {
                v___x_981_ = lean_box((v___x_939_) as usize);
                if v_isShared_980_ == 0 {
                    lean_ctor_set(v___x_979_, 0, v___x_981_);
                    v___x_983_ = v___x_979_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
                    v___x_983_ = v_reuseFailAlloc_984_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_983_;
            }
            5 => {
                if v_isShared_990_ == 0 {
                    v___x_992_ = v___x_989_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
                    v___x_992_ = v_reuseFailAlloc_993_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_992_;
            }
            7 => {
                v___x_1014_ = lean_box((v___x_939_) as usize);
                if v_isShared_1013_ == 0 {
                    lean_ctor_set(v___x_1012_, 0, v___x_1014_);
                    v___x_1016_ = v___x_1012_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
                    v___x_1016_ = v_reuseFailAlloc_1017_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1016_;
            }
            9 => {
                if v_isShared_1023_ == 0 {
                    v___x_1025_ = v___x_1022_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
                    v___x_1025_ = v_reuseFailAlloc_1026_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1025_;
            }
            11 => {
                if v_isShared_1032_ == 0 {
                    v___x_1034_ = v___x_1031_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
                    v___x_1034_ = v_reuseFailAlloc_1035_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1034_;
            }
            13 => {
                if lean_obj_tag(v_gs_1038_) == 1 {
                    v_head_1042_ = lean_ctor_get(v_gs_1038_, 0);
                    v_isSharedCheck_1082_ = (!lean_is_exclusive(v_gs_1038_)) as u8;
                    if v_isSharedCheck_1082_ == 0 {
                        v_unused_1083_ = lean_ctor_get(v_gs_1038_, 1);
                        lean_dec(v_unused_1083_);
                        v___x_1044_ = v_gs_1038_;
                        v_isShared_1045_ = v_isSharedCheck_1082_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_head_1042_);
                        lean_dec(v_gs_1038_);
                        v___x_1044_ = lean_box(0);
                        v_isShared_1045_ = v_isSharedCheck_1082_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1040_);
                    lean_dec(v_gs_1038_);
                    v___x_1084_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8_once), _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__8);
                    v___x_1085_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(v___x_1084_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
                    return v___x_1085_;
                }
            }
            14 => {
                if v_isShared_1041_ == 0 {
                    lean_ctor_set(v___x_1040_, 0, v_head_1042_);
                    v___x_1047_ = v___x_1040_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_head_1042_);
                    v___x_1047_ = v_reuseFailAlloc_1081_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_1048_ = l_Lean_Meta_Grind_mkResult(
                    v_params_940_,
                    v___x_1047_,
                    v___y_941_,
                    v___y_942_,
                    v___y_943_,
                    v___y_944_,
                    v___y_945_,
                    v___y_946_,
                    v___y_947_,
                    v___y_948_,
                    v___y_949_,
                );
                if lean_obj_tag(v___x_1048_) == 0 {
                    v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
                    lean_inc(v_a_1049_);
                    lean_dec_ref_known(v___x_1048_, 1);
                    v___x_1050_ = l_Lean_Meta_Grind_Result_toMessageData(
                        v_a_1049_, v___y_946_, v___y_947_, v___y_948_, v___y_949_,
                    );
                    if lean_obj_tag(v___x_1050_) == 0 {
                        v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
                        lean_inc(v_a_1051_);
                        lean_dec_ref_known(v___x_1050_, 1);
                        v___x_1052_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6_once), _init_l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___closed__6);
                        if v_isShared_1045_ == 0 {
                            lean_ctor_set_tag(v___x_1044_, 7);
                            lean_ctor_set(v___x_1044_, 1, v_a_1051_);
                            lean_ctor_set(v___x_1044_, 0, v___x_1052_);
                            v___x_1054_ = v___x_1044_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_1064_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1052_);
                            lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_a_1051_);
                            v___x_1054_ = v_reuseFailAlloc_1064_;
                            state = 16;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1044_);
                        v_a_1065_ = lean_ctor_get(v___x_1050_, 0);
                        v_isSharedCheck_1072_ = (!lean_is_exclusive(v___x_1050_)) as u8;
                        if v_isSharedCheck_1072_ == 0 {
                            v___x_1067_ = v___x_1050_;
                            v_isShared_1068_ = v_isSharedCheck_1072_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_1065_);
                            lean_dec(v___x_1050_);
                            v___x_1067_ = lean_box(0);
                            v_isShared_1068_ = v_isSharedCheck_1072_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1044_);
                    v_a_1073_ = lean_ctor_get(v___x_1048_, 0);
                    v_isSharedCheck_1080_ = (!lean_is_exclusive(v___x_1048_)) as u8;
                    if v_isSharedCheck_1080_ == 0 {
                        v___x_1075_ = v___x_1048_;
                        v_isShared_1076_ = v_isSharedCheck_1080_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_1073_);
                        lean_dec(v___x_1048_);
                        v___x_1075_ = lean_box(0);
                        v_isShared_1076_ = v_isSharedCheck_1080_;
                        state = 21;
                        continue;
                    }
                }
            }
            16 => {
                v___x_1055_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(v___x_1054_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
                v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
                v_isSharedCheck_1063_ = (!lean_is_exclusive(v___x_1055_)) as u8;
                if v_isSharedCheck_1063_ == 0 {
                    v___x_1058_ = v___x_1055_;
                    v_isShared_1059_ = v_isSharedCheck_1063_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_a_1056_);
                    lean_dec(v___x_1055_);
                    v___x_1058_ = lean_box(0);
                    v_isShared_1059_ = v_isSharedCheck_1063_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_1059_ == 0 {
                    v___x_1061_ = v___x_1058_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
                    v___x_1061_ = v_reuseFailAlloc_1062_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1061_;
            }
            19 => {
                if v_isShared_1068_ == 0 {
                    v___x_1070_ = v___x_1067_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
                    v___x_1070_ = v_reuseFailAlloc_1071_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1070_;
            }
            21 => {
                if v_isShared_1076_ == 0 {
                    v___x_1078_ = v___x_1075_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1078_;
            }
            23 => {
                if v_isShared_1090_ == 0 {
                    v___x_1092_ = v___x_1089_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
                    v___x_1092_ = v_reuseFailAlloc_1093_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1092_;
            }
            25 => {
                if v_isShared_1098_ == 0 {
                    v___x_1100_ = v___x_1097_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
                    v___x_1100_ = v_reuseFailAlloc_1101_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1103_: *mut LeanObject = *_args.add(0);
    let mut v_a_1104_: *mut LeanObject = *_args.add(1);
    let mut v___x_1105_: *mut LeanObject = *_args.add(2);
    let mut v___x_1106_: *mut LeanObject = *_args.add(3);
    let mut v___x_1107_: *mut LeanObject = *_args.add(4);
    let mut v___x_1108_: *mut LeanObject = *_args.add(5);
    let mut v_stx_1109_: *mut LeanObject = *_args.add(6);
    let mut v___x_1110_: *mut LeanObject = *_args.add(7);
    let mut v_params_1111_: *mut LeanObject = *_args.add(8);
    let mut v___y_1112_: *mut LeanObject = *_args.add(9);
    let mut v___y_1113_: *mut LeanObject = *_args.add(10);
    let mut v___y_1114_: *mut LeanObject = *_args.add(11);
    let mut v___y_1115_: *mut LeanObject = *_args.add(12);
    let mut v___y_1116_: *mut LeanObject = *_args.add(13);
    let mut v___y_1117_: *mut LeanObject = *_args.add(14);
    let mut v___y_1118_: *mut LeanObject = *_args.add(15);
    let mut v___y_1119_: *mut LeanObject = *_args.add(16);
    let mut v___y_1120_: *mut LeanObject = *_args.add(17);
    let mut v___y_1121_: *mut LeanObject = *_args.add(18);
    let mut v___x_23416__boxed_1122_: u8 = 0;
    let mut v_res_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_23416__boxed_1122_ = (lean_unbox(v___x_1110_) as u8);
    v_res_1123_ =
        l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0(
            v_a_1103_,
            v_a_1104_,
            v___x_1105_,
            v___x_1106_,
            v___x_1107_,
            v___x_1108_,
            v_stx_1109_,
            v___x_23416__boxed_1122_,
            v_params_1111_,
            v___y_1112_,
            v___y_1113_,
            v___y_1114_,
            v___y_1115_,
            v___y_1116_,
            v___y_1117_,
            v___y_1118_,
            v___y_1119_,
            v___y_1120_,
        );
    lean_dec(v___y_1120_);
    lean_dec_ref(v___y_1119_);
    lean_dec(v___y_1118_);
    lean_dec_ref(v___y_1117_);
    lean_dec(v___y_1116_);
    lean_dec_ref(v___y_1115_);
    lean_dec(v___y_1114_);
    lean_dec_ref(v___y_1113_);
    lean_dec(v___y_1112_);
    lean_dec_ref(v_params_1111_);
    return v_res_1123_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(
    mut v___f_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1138_: u8 = 0;
    let mut v___x_1139_: u8 = 0;
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1146_: u8 = 0;
    let mut v_a_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1154_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1134_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(
                    v___f_1124_,
                    v___y_1125_,
                    v___y_1126_,
                    v___y_1129_,
                    v___y_1130_,
                    v___y_1131_,
                    v___y_1132_,
                );
                if lean_obj_tag(v___x_1134_) == 0 {
                    v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
                    v_isSharedCheck_1146_ = (!lean_is_exclusive(v___x_1134_)) as u8;
                    if v_isSharedCheck_1146_ == 0 {
                        v___x_1137_ = v___x_1134_;
                        v_isShared_1138_ = v_isSharedCheck_1146_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1135_);
                        lean_dec(v___x_1134_);
                        v___x_1137_ = lean_box(0);
                        v_isShared_1138_ = v_isSharedCheck_1146_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1147_ = lean_ctor_get(v___x_1134_, 0);
                    v_isSharedCheck_1154_ = (!lean_is_exclusive(v___x_1134_)) as u8;
                    if v_isSharedCheck_1154_ == 0 {
                        v___x_1149_ = v___x_1134_;
                        v_isShared_1150_ = v_isSharedCheck_1154_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1147_);
                        lean_dec(v___x_1134_);
                        v___x_1149_ = lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1154_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1139_ = (lean_unbox(v_a_1135_) as u8);
                lean_dec(v_a_1135_);
                if v___x_1139_ == 0 {
                    v___x_1140_ = lean_box(0);
                    if v_isShared_1138_ == 0 {
                        lean_ctor_set(v___x_1137_, 0, v___x_1140_);
                        v___x_1142_ = v___x_1137_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
                        v___x_1142_ = v_reuseFailAlloc_1143_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1137_);
                    v___x_1144_ = lean_box(0);
                    v___x_1145_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(
                        v___x_1144_,
                        v___y_1126_,
                        v___y_1129_,
                        v___y_1130_,
                        v___y_1131_,
                        v___y_1132_,
                    );
                    return v___x_1145_;
                }
            }
            2 => {
                return v___x_1142_;
            }
            3 => {
                if v_isShared_1150_ == 0 {
                    v___x_1152_ = v___x_1149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
                    v___x_1152_ = v_reuseFailAlloc_1153_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed(
    mut v___f_1155_: *mut LeanObject,
    mut v___y_1156_: *mut LeanObject,
    mut v___y_1157_: *mut LeanObject,
    mut v___y_1158_: *mut LeanObject,
    mut v___y_1159_: *mut LeanObject,
    mut v___y_1160_: *mut LeanObject,
    mut v___y_1161_: *mut LeanObject,
    mut v___y_1162_: *mut LeanObject,
    mut v___y_1163_: *mut LeanObject,
    mut v___y_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1165_: *mut LeanObject = core::ptr::null_mut();
    v_res_1165_ =
        l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1(
            v___f_1155_,
            v___y_1156_,
            v___y_1157_,
            v___y_1158_,
            v___y_1159_,
            v___y_1160_,
            v___y_1161_,
            v___y_1162_,
            v___y_1163_,
        );
    lean_dec(v___y_1163_);
    lean_dec_ref(v___y_1162_);
    lean_dec(v___y_1161_);
    lean_dec_ref(v___y_1160_);
    lean_dec(v___y_1159_);
    lean_dec_ref(v___y_1158_);
    lean_dec(v___y_1157_);
    lean_dec_ref(v___y_1156_);
    return v_res_1165_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(
    mut v___x_1166_: *mut LeanObject,
    mut v___x_1167_: *mut LeanObject,
    mut v___x_1168_: *mut LeanObject,
    mut v___x_1169_: *mut LeanObject,
    mut v___x_1170_: *mut LeanObject,
    mut v_stx_1171_: *mut LeanObject,
    mut v___x_1172_: u8,
    mut v___y_1173_: *mut LeanObject,
    mut v___y_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
    mut v___y_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
    mut v___y_1179_: *mut LeanObject,
    mut v___y_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1194_: u8 = 0;
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1198_: u8 = 0;
    let mut v_a_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1202_: u8 = 0;
    let mut v_ref_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1182_ = l_Lean_Meta_Grind_Action_mkFinish(v___x_1166_);
                if lean_obj_tag(v___x_1182_) == 0 {
                    v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
                    lean_inc(v_a_1183_);
                    lean_dec_ref_known(v___x_1182_, 1);
                    v___x_1184_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(
                        v___y_1174_,
                        v___y_1177_,
                        v___y_1178_,
                        v___y_1179_,
                        v___y_1180_,
                    );
                    if lean_obj_tag(v___x_1184_) == 0 {
                        v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
                        lean_inc(v_a_1185_);
                        lean_dec_ref_known(v___x_1184_, 1);
                        v_params_1186_ = lean_ctor_get(v___y_1173_, 4);
                        v___x_1187_ = lean_box((v___x_1172_) as usize);
                        lean_inc_ref(v_params_1186_);
                        v___f_1188_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__0___boxed as *mut core::ffi::c_void, 19, 9);
                        lean_closure_set(v___f_1188_, 0, v_a_1185_);
                        lean_closure_set(v___f_1188_, 1, v_a_1183_);
                        lean_closure_set(v___f_1188_, 2, v___x_1167_);
                        lean_closure_set(v___f_1188_, 3, v___x_1168_);
                        lean_closure_set(v___f_1188_, 4, v___x_1169_);
                        lean_closure_set(v___f_1188_, 5, v___x_1170_);
                        lean_closure_set(v___f_1188_, 6, v_stx_1171_);
                        lean_closure_set(v___f_1188_, 7, v___x_1187_);
                        lean_closure_set(v___f_1188_, 8, v_params_1186_);
                        v___f_1189_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__1___boxed as *mut core::ffi::c_void, 10, 1);
                        lean_closure_set(v___f_1189_, 0, v___f_1188_);
                        v___x_1190_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_withTracing___redArg(v___f_1189_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
                        lean_dec_ref(v___y_1173_);
                        return v___x_1190_;
                    } else {
                        lean_dec(v_a_1183_);
                        lean_dec_ref(v___y_1173_);
                        lean_dec(v_stx_1171_);
                        lean_dec_ref(v___x_1170_);
                        lean_dec_ref(v___x_1169_);
                        lean_dec_ref(v___x_1168_);
                        lean_dec_ref(v___x_1167_);
                        v_a_1191_ = lean_ctor_get(v___x_1184_, 0);
                        v_isSharedCheck_1198_ = (!lean_is_exclusive(v___x_1184_)) as u8;
                        if v_isSharedCheck_1198_ == 0 {
                            v___x_1193_ = v___x_1184_;
                            v_isShared_1194_ = v_isSharedCheck_1198_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1191_);
                            lean_dec(v___x_1184_);
                            v___x_1193_ = lean_box(0);
                            v_isShared_1194_ = v_isSharedCheck_1198_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_1173_);
                    lean_dec(v_stx_1171_);
                    lean_dec_ref(v___x_1170_);
                    lean_dec_ref(v___x_1169_);
                    lean_dec_ref(v___x_1168_);
                    lean_dec_ref(v___x_1167_);
                    v_a_1199_ = lean_ctor_get(v___x_1182_, 0);
                    v_isSharedCheck_1211_ = (!lean_is_exclusive(v___x_1182_)) as u8;
                    if v_isSharedCheck_1211_ == 0 {
                        v___x_1201_ = v___x_1182_;
                        v_isShared_1202_ = v_isSharedCheck_1211_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1199_);
                        lean_dec(v___x_1182_);
                        v___x_1201_ = lean_box(0);
                        v_isShared_1202_ = v_isSharedCheck_1211_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1194_ == 0 {
                    v___x_1196_ = v___x_1193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
                    v___x_1196_ = v_reuseFailAlloc_1197_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1196_;
            }
            3 => {
                v_ref_1203_ = lean_ctor_get(v___y_1179_, 5);
                v___x_1204_ = lean_io_error_to_string(v_a_1199_);
                v___x_1205_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1205_, 0, v___x_1204_);
                v___x_1206_ = l_Lean_MessageData_ofFormat(v___x_1205_);
                lean_inc(v_ref_1203_);
                v___x_1207_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1207_, 0, v_ref_1203_);
                lean_ctor_set(v___x_1207_, 1, v___x_1206_);
                if v_isShared_1202_ == 0 {
                    lean_ctor_set(v___x_1201_, 0, v___x_1207_);
                    v___x_1209_ = v___x_1201_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
                    v___x_1209_ = v_reuseFailAlloc_1210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed(
    mut v___x_1212_: *mut LeanObject,
    mut v___x_1213_: *mut LeanObject,
    mut v___x_1214_: *mut LeanObject,
    mut v___x_1215_: *mut LeanObject,
    mut v___x_1216_: *mut LeanObject,
    mut v_stx_1217_: *mut LeanObject,
    mut v___x_1218_: *mut LeanObject,
    mut v___y_1219_: *mut LeanObject,
    mut v___y_1220_: *mut LeanObject,
    mut v___y_1221_: *mut LeanObject,
    mut v___y_1222_: *mut LeanObject,
    mut v___y_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_23859__boxed_1228_: u8 = 0;
    let mut v_res_1229_: *mut LeanObject = core::ptr::null_mut();
    v___x_23859__boxed_1228_ = (lean_unbox(v___x_1218_) as u8);
    v_res_1229_ =
        l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2(
            v___x_1212_,
            v___x_1213_,
            v___x_1214_,
            v___x_1215_,
            v___x_1216_,
            v_stx_1217_,
            v___x_23859__boxed_1228_,
            v___y_1219_,
            v___y_1220_,
            v___y_1221_,
            v___y_1222_,
            v___y_1223_,
            v___y_1224_,
            v___y_1225_,
            v___y_1226_,
        );
    lean_dec(v___y_1226_);
    lean_dec_ref(v___y_1225_);
    lean_dec(v___y_1224_);
    lean_dec_ref(v___y_1223_);
    lean_dec(v___y_1222_);
    lean_dec_ref(v___y_1221_);
    lean_dec(v___y_1220_);
    return v_res_1229_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(
    mut v___y_1230_: *mut LeanObject,
    mut v___x_1231_: *mut LeanObject,
    mut v___x_1232_: *mut LeanObject,
    mut v___x_1233_: *mut LeanObject,
    mut v___x_1234_: *mut LeanObject,
    mut v_stx_1235_: *mut LeanObject,
    mut v___x_1236_: u8,
    mut v_only_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1250_: u8 = 0;
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_1247_ = lean_ctor_get(v___y_1238_, 4);
                lean_inc_ref(v_params_1247_);
                v___x_1248_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1230_);
                if lean_obj_tag(v_only_1237_) == 0 {
                    v___x_1255_ = 0;
                    v___y_1250_ = v___x_1255_;
                    state = 1;
                    continue;
                } else {
                    v___y_1250_ = v___x_1236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1251_ = lean_unsigned_to_nat(10000);
                v___x_1252_ = lean_box((v___x_1236_) as usize);
                v___f_1253_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__2___boxed as *mut core::ffi::c_void, 16, 7);
                lean_closure_set(v___f_1253_, 0, v___x_1251_);
                lean_closure_set(v___f_1253_, 1, v___x_1231_);
                lean_closure_set(v___f_1253_, 2, v___x_1232_);
                lean_closure_set(v___f_1253_, 3, v___x_1233_);
                lean_closure_set(v___f_1253_, 4, v___x_1234_);
                lean_closure_set(v___f_1253_, 5, v_stx_1235_);
                lean_closure_set(v___f_1253_, 6, v___x_1252_);
                v___x_1254_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(
                    v_params_1247_,
                    v___x_1248_,
                    v___y_1250_,
                    v___f_1253_,
                    v___y_1238_,
                    v___y_1239_,
                    v___y_1240_,
                    v___y_1241_,
                    v___y_1242_,
                    v___y_1243_,
                    v___y_1244_,
                    v___y_1245_,
                );
                lean_dec_ref(v___y_1238_);
                lean_dec_ref(v___x_1248_);
                return v___x_1254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1256_: *mut LeanObject = *_args.add(0);
    let mut v___x_1257_: *mut LeanObject = *_args.add(1);
    let mut v___x_1258_: *mut LeanObject = *_args.add(2);
    let mut v___x_1259_: *mut LeanObject = *_args.add(3);
    let mut v___x_1260_: *mut LeanObject = *_args.add(4);
    let mut v_stx_1261_: *mut LeanObject = *_args.add(5);
    let mut v___x_1262_: *mut LeanObject = *_args.add(6);
    let mut v_only_1263_: *mut LeanObject = *_args.add(7);
    let mut v___y_1264_: *mut LeanObject = *_args.add(8);
    let mut v___y_1265_: *mut LeanObject = *_args.add(9);
    let mut v___y_1266_: *mut LeanObject = *_args.add(10);
    let mut v___y_1267_: *mut LeanObject = *_args.add(11);
    let mut v___y_1268_: *mut LeanObject = *_args.add(12);
    let mut v___y_1269_: *mut LeanObject = *_args.add(13);
    let mut v___y_1270_: *mut LeanObject = *_args.add(14);
    let mut v___y_1271_: *mut LeanObject = *_args.add(15);
    let mut v___y_1272_: *mut LeanObject = *_args.add(16);
    let mut v___x_23960__boxed_1273_: u8 = 0;
    let mut v_res_1274_: *mut LeanObject = core::ptr::null_mut();
    v___x_23960__boxed_1273_ = (lean_unbox(v___x_1262_) as u8);
    v_res_1274_ =
        l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3(
            v___y_1256_,
            v___x_1257_,
            v___x_1258_,
            v___x_1259_,
            v___x_1260_,
            v_stx_1261_,
            v___x_23960__boxed_1273_,
            v_only_1263_,
            v___y_1264_,
            v___y_1265_,
            v___y_1266_,
            v___y_1267_,
            v___y_1268_,
            v___y_1269_,
            v___y_1270_,
            v___y_1271_,
        );
    lean_dec(v___y_1271_);
    lean_dec_ref(v___y_1270_);
    lean_dec(v___y_1269_);
    lean_dec_ref(v___y_1268_);
    lean_dec(v___y_1267_);
    lean_dec_ref(v___y_1266_);
    lean_dec(v___y_1265_);
    lean_dec(v_only_1263_);
    lean_dec_ref(v___y_1256_);
    return v_res_1274_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(
    mut v_sz_1275_: usize,
    mut v_i_1276_: usize,
    mut v_bs_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1278_: u8 = 0;
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: usize = 0;
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1278_ = lean_usize_dec_lt(v_i_1276_, v_sz_1275_);
                if v___x_1278_ == 0 {
                    v___x_1279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1279_, 0, v_bs_1277_);
                    return v___x_1279_;
                } else {
                    v_v_1280_ = lean_array_uget(v_bs_1277_, v_i_1276_);
                    v___x_1281_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1282_ = lean_array_uset(v_bs_1277_, v_i_1276_, v___x_1281_);
                    v___x_1283_ = 1usize;
                    v___x_1284_ = lean_usize_add(v_i_1276_, v___x_1283_);
                    v___x_1285_ = lean_array_uset(v_bs_x27_1282_, v_i_1276_, v_v_1280_);
                    v_i_1276_ = v___x_1284_;
                    v_bs_1277_ = v___x_1285_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1___boxed(
    mut v_sz_1287_: *mut LeanObject,
    mut v_i_1288_: *mut LeanObject,
    mut v_bs_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1290_: usize = 0;
    let mut v_i_boxed_1291_: usize = 0;
    let mut v_res_1292_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1290_ = lean_unbox_usize(v_sz_1287_);
    lean_dec(v_sz_1287_);
    v_i_boxed_1291_ = lean_unbox_usize(v_i_1288_);
    lean_dec(v_i_1288_);
    v_res_1292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_boxed_1290_, v_i_boxed_1291_, v_bs_1289_);
    return v_res_1292_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(
    mut v_stx_1306_: *mut LeanObject,
    mut v_a_1307_: *mut LeanObject,
    mut v_a_1308_: *mut LeanObject,
    mut v_a_1309_: *mut LeanObject,
    mut v_a_1310_: *mut LeanObject,
    mut v_a_1311_: *mut LeanObject,
    mut v_a_1312_: *mut LeanObject,
    mut v_a_1313_: *mut LeanObject,
    mut v_a_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1326_: usize = 0;
    let mut v___x_1327_: usize = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v___y_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_only_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_x3f_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_only_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1316_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__0;
                v___x_1317_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__1;
                v___x_1318_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__2;
                v___x_1319_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__3;
                v___x_1320_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5;
                lean_inc(v_stx_1306_);
                v___x_1321_ = l_Lean_Syntax_isOfKind(v_stx_1306_, v___x_1320_);
                if v___x_1321_ == 0 {
                    lean_dec(v_stx_1306_);
                    v___x_1322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
                    return v___x_1322_;
                } else {
                    v___x_1323_ = lean_unsigned_to_nat(1);
                    v___x_1324_ = l_Lean_Syntax_getArg(v_stx_1306_, v___x_1323_);
                    v___x_1325_ = l_Lean_Syntax_getArgs(v___x_1324_);
                    lean_dec(v___x_1324_);
                    v_sz_1326_ = lean_array_size(v___x_1325_);
                    v___x_1327_ = 0usize;
                    v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__1(v_sz_1326_, v___x_1327_, v___x_1325_);
                    if lean_obj_tag(v___x_1328_) == 0 {
                        lean_dec(v_stx_1306_);
                        v___x_1329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
                        return v___x_1329_;
                    } else {
                        v_val_1330_ = lean_ctor_get(v___x_1328_, 0);
                        v_isSharedCheck_1377_ = (!lean_is_exclusive(v___x_1328_)) as u8;
                        if v_isSharedCheck_1377_ == 0 {
                            v___x_1332_ = v___x_1328_;
                            v_isShared_1333_ = v_isSharedCheck_1377_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1330_);
                            lean_dec(v___x_1328_);
                            v___x_1332_ = lean_box(0);
                            v_isShared_1333_ = v_isSharedCheck_1377_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1366_ = lean_unsigned_to_nat(2);
                v___x_1367_ = l_Lean_Syntax_getArg(v_stx_1306_, v___x_1366_);
                v___x_1368_ = l_Lean_Syntax_isNone(v___x_1367_);
                if v___x_1368_ == 0 {
                    lean_inc(v___x_1367_);
                    v___x_1369_ = l_Lean_Syntax_matchesNull(v___x_1367_, v___x_1323_);
                    if v___x_1369_ == 0 {
                        lean_dec(v___x_1367_);
                        lean_del_object(v___x_1332_);
                        lean_dec(v_val_1330_);
                        lean_dec(v_stx_1306_);
                        v___x_1370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
                        return v___x_1370_;
                    } else {
                        v___x_1371_ = lean_unsigned_to_nat(0);
                        v_only_1372_ = l_Lean_Syntax_getArg(v___x_1367_, v___x_1371_);
                        lean_dec(v___x_1367_);
                        if v_isShared_1333_ == 0 {
                            lean_ctor_set(v___x_1332_, 0, v_only_1372_);
                            v___x_1374_ = v___x_1332_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_only_1372_);
                            v___x_1374_ = v_reuseFailAlloc_1375_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1367_);
                    lean_del_object(v___x_1332_);
                    v___x_1376_ = lean_box(0);
                    v_only_1349_ = v___x_1376_;
                    v___y_1350_ = v_a_1307_;
                    v___y_1351_ = v_a_1308_;
                    v___y_1352_ = v_a_1309_;
                    v___y_1353_ = v_a_1310_;
                    v___y_1354_ = v_a_1311_;
                    v___y_1355_ = v_a_1312_;
                    v___y_1356_ = v_a_1313_;
                    v___y_1357_ = v_a_1314_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                v___x_1345_ = lean_box((v___x_1321_) as usize);
                v___f_1346_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___lam__3___boxed as *mut core::ffi::c_void, 17, 8);
                lean_closure_set(v___f_1346_, 0, v___y_1344_);
                lean_closure_set(v___f_1346_, 1, v___x_1316_);
                lean_closure_set(v___f_1346_, 2, v___x_1317_);
                lean_closure_set(v___f_1346_, 3, v___x_1318_);
                lean_closure_set(v___f_1346_, 4, v___x_1319_);
                lean_closure_set(v___f_1346_, 5, v_stx_1306_);
                lean_closure_set(v___f_1346_, 6, v___x_1345_);
                lean_closure_set(v___f_1346_, 7, v___y_1335_);
                v___x_1347_ = l_Lean_Elab_Tactic_Grind_withConfigItems___redArg(
                    v_val_1330_,
                    v___f_1346_,
                    v___y_1336_,
                    v___y_1341_,
                    v___y_1343_,
                    v___y_1340_,
                    v___y_1339_,
                    v___y_1337_,
                    v___y_1342_,
                    v___y_1338_,
                );
                return v___x_1347_;
            }
            3 => {
                v___x_1358_ = lean_unsigned_to_nat(3);
                v___x_1359_ = l_Lean_Syntax_getArg(v_stx_1306_, v___x_1358_);
                v___x_1360_ = l_Lean_Syntax_isNone(v___x_1359_);
                if v___x_1360_ == 0 {
                    lean_inc(v___x_1359_);
                    v___x_1361_ = l_Lean_Syntax_matchesNull(v___x_1359_, v___x_1358_);
                    if v___x_1361_ == 0 {
                        lean_dec(v___x_1359_);
                        lean_dec(v_only_1349_);
                        lean_dec(v_val_1330_);
                        lean_dec(v_stx_1306_);
                        v___x_1362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__0___redArg();
                        return v___x_1362_;
                    } else {
                        v___x_1363_ = l_Lean_Syntax_getArg(v___x_1359_, v___x_1323_);
                        lean_dec(v___x_1359_);
                        v_params_x3f_1364_ = l_Lean_Syntax_getArgs(v___x_1363_);
                        lean_dec(v___x_1363_);
                        v___y_1335_ = v_only_1349_;
                        v___y_1336_ = v___y_1350_;
                        v___y_1337_ = v___y_1355_;
                        v___y_1338_ = v___y_1357_;
                        v___y_1339_ = v___y_1354_;
                        v___y_1340_ = v___y_1353_;
                        v___y_1341_ = v___y_1351_;
                        v___y_1342_ = v___y_1356_;
                        v___y_1343_ = v___y_1352_;
                        v___y_1344_ = v_params_x3f_1364_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1359_);
                    v___x_1365_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__6;
                    v___y_1335_ = v_only_1349_;
                    v___y_1336_ = v___y_1350_;
                    v___y_1337_ = v___y_1355_;
                    v___y_1338_ = v___y_1357_;
                    v___y_1339_ = v___y_1354_;
                    v___y_1340_ = v___y_1353_;
                    v___y_1341_ = v___y_1351_;
                    v___y_1342_ = v___y_1356_;
                    v___y_1343_ = v___y_1352_;
                    v___y_1344_ = v___x_1365_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_only_1349_ = v___x_1374_;
                v___y_1350_ = v_a_1307_;
                v___y_1351_ = v_a_1308_;
                v___y_1352_ = v_a_1309_;
                v___y_1353_ = v_a_1310_;
                v___y_1354_ = v_a_1311_;
                v___y_1355_ = v_a_1312_;
                v___y_1356_ = v_a_1313_;
                v___y_1357_ = v_a_1314_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed(
    mut v_stx_1378_: *mut LeanObject,
    mut v_a_1379_: *mut LeanObject,
    mut v_a_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1388_: *mut LeanObject = core::ptr::null_mut();
    v_res_1388_ =
        l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace(
            v_stx_1378_,
            v_a_1379_,
            v_a_1380_,
            v_a_1381_,
            v_a_1382_,
            v_a_1383_,
            v_a_1384_,
            v_a_1385_,
            v_a_1386_,
        );
    lean_dec(v_a_1386_);
    lean_dec_ref(v_a_1385_);
    lean_dec(v_a_1384_);
    lean_dec_ref(v_a_1383_);
    lean_dec(v_a_1382_);
    lean_dec_ref(v_a_1381_);
    lean_dec(v_a_1380_);
    lean_dec_ref(v_a_1379_);
    return v_res_1388_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(
    mut v_00_u03b1_1389_: *mut LeanObject,
    mut v_msg_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
    mut v___y_1394_: *mut LeanObject,
    mut v___y_1395_: *mut LeanObject,
    mut v___y_1396_: *mut LeanObject,
    mut v___y_1397_: *mut LeanObject,
    mut v___y_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___redArg(v_msg_1390_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
    return v___x_1401_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2___boxed(
    mut v_00_u03b1_1402_: *mut LeanObject,
    mut v_msg_1403_: *mut LeanObject,
    mut v___y_1404_: *mut LeanObject,
    mut v___y_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
    mut v___y_1412_: *mut LeanObject,
    mut v___y_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace_spec__2(v_00_u03b1_1402_, v_msg_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
    lean_dec(v___y_1412_);
    lean_dec_ref(v___y_1411_);
    lean_dec(v___y_1410_);
    lean_dec_ref(v___y_1409_);
    lean_dec(v___y_1408_);
    lean_dec_ref(v___y_1407_);
    lean_dec(v___y_1406_);
    lean_dec_ref(v___y_1405_);
    lean_dec(v___y_1404_);
    return v_res_1414_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1()
-> *mut LeanObject {
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    v___x_1456_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_1457_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___closed__5;
    v___x_1458_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___closed__15;
    v___x_1459_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1460_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1456_,
        v___x_1457_,
        v___x_1458_,
        v___x_1459_,
    );
    return v___x_1460_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1___boxed(
    mut v_a_1461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1462_: *mut LeanObject = core::ptr::null_mut();
    v_res_1462_ = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
    return v_res_1462_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Param(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace___regBuiltin___private_Lean_Elab_Tactic_Grind_Trace_0__Lean_Elab_Tactic_Grind_evalFinishTrace__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_Trace(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Param(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
}
