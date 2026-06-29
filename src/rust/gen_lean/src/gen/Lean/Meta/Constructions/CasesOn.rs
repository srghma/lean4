// Lean compiler output
// Module: Lean.Meta.Constructions.CasesOn
// Imports: Init.Data.Range.Basic Lean.Meta.Basic Lean.AddDecl
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_expr_instantiate1, lean_float_decLt, lean_float_div, lean_float_sub, lean_infer_type,
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_range, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Range::Basic::{
    initialize_Init_Data_Range_Basic, runtime_initialize_Init_Data_Range_Basic,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_str___override, l_Lean_replaceRef, l_List_lengthTR___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addDecl, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::AuxRecursor::{
    l_Lean_casesOnSuffix, l_Lean_markAuxRecursor, l_Lean_mkCasesOnName,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_enableRealizationsForConst,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type, l_Lean_mkRecName,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_instBEqFVarId_beq,
    l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_binderInfo, l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReducibilityAttrs::l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_registerTraceClass, l_Lean_trace_profiler, l_Lean_trace_profiler_threshold,
    l_Lean_trace_profiler_useHeartbeats,
};
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__2_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__3_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 114, 114, 111, 114, 32, 105, 110, 32, 39, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [39, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 44, 32, 39, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__7_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [39, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__3_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 101, 97, 110, 46, 105, 115, 82, 101, 99, 63, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__4_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [80, 85, 110, 105, 116, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0_value) as *mut crate::leanh::LeanObject,11091137386503903511 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 110, 105, 116, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__0_value) as *mut crate::leanh::LeanObject,11091137386503903511 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__2_value) as *mut crate::leanh::LeanObject,14036392901208071058 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__3_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5: f64 = 0.0;
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkCasesOn___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [77, 101, 116, 97, 0],
    };
static mut l_Lean_mkCasesOn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOn___closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [109, 107, 67, 97, 115, 101, 115, 79, 110, 0],
    };
static mut l_Lean_mkCasesOn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_mkCasesOn___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_mkCasesOn___closed__0_value)
                as *mut crate::leanh::LeanObject,
            142734480563613395 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_mkCasesOn___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_mkCasesOn___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_mkCasesOn___closed__1_value)
                as *mut crate::leanh::LeanObject,
            14554705660503211730 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkCasesOn___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOn___closed__3_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lean_mkCasesOn___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOn___closed__4_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_mkCasesOn___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOn___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_mkCasesOn___closed__4_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkCasesOn___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOn___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkCasesOn___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkCasesOn___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkCasesOn___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkCasesOn___closed__7: f64 = 0.0;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkCasesOn___closed__0_value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6298619751691480032 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 97, 115, 101, 115, 79, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13908150127721417385 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14330104791255047660 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16850664713141342957 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5363805602364615876 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6817493867345643597 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6919186570005574456 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_mkCasesOn___closed__0_value) as *mut crate::leanh::LeanObject,12403985358287198356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15944516466164890162 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3279181264441860707 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 989523109 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,13719880224209321761 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15756402433763682466 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15912005368295936558 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10514961098779268799 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___lam__0(
    mut v_k_2935_: *mut crate::leanh::LeanObject,
    mut v_b_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
    mut v___y_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2940_);
    crate::leanh::lean_inc_ref(v___y_2939_);
    crate::leanh::lean_inc(v___y_2938_);
    crate::leanh::lean_inc_ref(v___y_2937_);
    v___x_2942_ = crate::leanh::lean_apply_6(
        v_k_2935_,
        v_b_2936_,
        v___y_2937_,
        v___y_2938_,
        v___y_2939_,
        v___y_2940_,
        crate::leanh::lean_box(0),
    );
    return v___x_2942_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___lam__0___boxed(
    mut v_k_2943_: *mut crate::leanh::LeanObject,
    mut v_b_2944_: *mut crate::leanh::LeanObject,
    mut v___y_2945_: *mut crate::leanh::LeanObject,
    mut v___y_2946_: *mut crate::leanh::LeanObject,
    mut v___y_2947_: *mut crate::leanh::LeanObject,
    mut v___y_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2950_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___lam__0(v_k_2943_, v_b_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
    crate::leanh::lean_dec(v___y_2948_);
    crate::leanh::lean_dec_ref(v___y_2947_);
    crate::leanh::lean_dec(v___y_2946_);
    crate::leanh::lean_dec_ref(v___y_2945_);
    return v_res_2950_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(
    mut v_name_2951_: *mut crate::leanh::LeanObject,
    mut v_bi_2952_: u8,
    mut v_type_2953_: *mut crate::leanh::LeanObject,
    mut v_k_2954_: *mut crate::leanh::LeanObject,
    mut v_kind_2955_: u8,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
    mut v___y_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_a_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2961_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_2961_, 0, v_k_2954_);
                v___x_2962_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_2951_,
                    v_bi_2952_,
                    v_type_2953_,
                    v___f_2961_,
                    v_kind_2955_,
                    v___y_2956_,
                    v___y_2957_,
                    v___y_2958_,
                    v___y_2959_,
                );
                if crate::leanh::lean_obj_tag(v___x_2962_) == 0 {
                    v_a_2963_ = crate::leanh::lean_ctor_get(v___x_2962_, 0);
                    v_isSharedCheck_2970_ = (!crate::leanh::lean_is_exclusive(v___x_2962_)) as u8;
                    if v_isSharedCheck_2970_ == 0 {
                        v___x_2965_ = v___x_2962_;
                        v_isShared_2966_ = v_isSharedCheck_2970_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2963_);
                        crate::leanh::lean_dec(v___x_2962_);
                        v___x_2965_ = crate::leanh::lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2970_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2971_ = crate::leanh::lean_ctor_get(v___x_2962_, 0);
                    v_isSharedCheck_2978_ = (!crate::leanh::lean_is_exclusive(v___x_2962_)) as u8;
                    if v_isSharedCheck_2978_ == 0 {
                        v___x_2973_ = v___x_2962_;
                        v_isShared_2974_ = v_isSharedCheck_2978_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2971_);
                        crate::leanh::lean_dec(v___x_2962_);
                        v___x_2973_ = crate::leanh::lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_2978_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2966_ == 0 {
                    v___x_2968_ = v___x_2965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
                    v___x_2968_ = v_reuseFailAlloc_2969_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2968_;
            }
            3 => {
                if v_isShared_2974_ == 0 {
                    v___x_2976_ = v___x_2973_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
                    v___x_2976_ = v_reuseFailAlloc_2977_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg___boxed(
    mut v_name_2979_: *mut crate::leanh::LeanObject,
    mut v_bi_2980_: *mut crate::leanh::LeanObject,
    mut v_type_2981_: *mut crate::leanh::LeanObject,
    mut v_k_2982_: *mut crate::leanh::LeanObject,
    mut v_kind_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
    mut v___y_2987_: *mut crate::leanh::LeanObject,
    mut v___y_2988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_2989_: u8 = 0;
    let mut v_kind_boxed_2990_: u8 = 0;
    let mut v_res_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2989_ = (crate::leanh::lean_unbox(v_bi_2980_) as u8);
    v_kind_boxed_2990_ = (crate::leanh::lean_unbox(v_kind_2983_) as u8);
    v_res_2991_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_name_2979_, v_bi_boxed_2989_, v_type_2981_, v_k_2982_, v_kind_boxed_2990_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
    crate::leanh::lean_dec(v___y_2987_);
    crate::leanh::lean_dec_ref(v___y_2986_);
    crate::leanh::lean_dec(v___y_2985_);
    crate::leanh::lean_dec_ref(v___y_2984_);
    return v_res_2991_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0(
    mut v_00_u03b1_2992_: *mut crate::leanh::LeanObject,
    mut v_name_2993_: *mut crate::leanh::LeanObject,
    mut v_bi_2994_: u8,
    mut v_type_2995_: *mut crate::leanh::LeanObject,
    mut v_k_2996_: *mut crate::leanh::LeanObject,
    mut v_kind_2997_: u8,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
    mut v___y_2999_: *mut crate::leanh::LeanObject,
    mut v___y_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3003_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_name_2993_, v_bi_2994_, v_type_2995_, v_k_2996_, v_kind_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
    return v___x_3003_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___boxed(
    mut v_00_u03b1_3004_: *mut crate::leanh::LeanObject,
    mut v_name_3005_: *mut crate::leanh::LeanObject,
    mut v_bi_3006_: *mut crate::leanh::LeanObject,
    mut v_type_3007_: *mut crate::leanh::LeanObject,
    mut v_k_3008_: *mut crate::leanh::LeanObject,
    mut v_kind_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3015_: u8 = 0;
    let mut v_kind_boxed_3016_: u8 = 0;
    let mut v_res_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3015_ = (crate::leanh::lean_unbox(v_bi_3006_) as u8);
    v_kind_boxed_3016_ = (crate::leanh::lean_unbox(v_kind_3009_) as u8);
    v_res_3017_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0(v_00_u03b1_3004_, v_name_3005_, v_bi_boxed_3015_, v_type_3007_, v_k_3008_, v_kind_boxed_3016_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
    crate::leanh::lean_dec(v___y_3013_);
    crate::leanh::lean_dec_ref(v___y_3012_);
    crate::leanh::lean_dec(v___y_3011_);
    crate::leanh::lean_dec_ref(v___y_3010_);
    return v_res_3017_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___lam__0(
    mut v_body_3018_: *mut crate::leanh::LeanObject,
    mut v_unit_3019_: *mut crate::leanh::LeanObject,
    mut v_x_3020_: *mut crate::leanh::LeanObject,
    mut v___y_3021_: *mut crate::leanh::LeanObject,
    mut v___y_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3026_ = lean_expr_instantiate1(v_body_3018_, v_x_3020_);
    v___x_3027_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit(
        v___x_3026_,
        v_unit_3019_,
        v___y_3021_,
        v___y_3022_,
        v___y_3023_,
        v___y_3024_,
    );
    if crate::leanh::lean_obj_tag(v___x_3027_) == 0 {
        let mut v_a_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3032_: u8 = 0;
        let mut v___x_3033_: u8 = 0;
        let mut v___x_3034_: u8 = 0;
        let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3028_ = crate::leanh::lean_ctor_get(v___x_3027_, 0);
        crate::leanh::lean_inc(v_a_3028_);
        crate::leanh::lean_dec_ref_known(v___x_3027_, 1);
        v___x_3029_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3030_ = lean_mk_empty_array_with_capacity(v___x_3029_);
        v___x_3031_ = lean_array_push(v___x_3030_, v_x_3020_);
        v___x_3032_ = 0;
        v___x_3033_ = 1;
        v___x_3034_ = 1;
        v___x_3035_ = l_Lean_Meta_mkForallFVars(
            v___x_3031_,
            v_a_3028_,
            v___x_3032_,
            v___x_3033_,
            v___x_3033_,
            v___x_3034_,
            v___y_3021_,
            v___y_3022_,
            v___y_3023_,
            v___y_3024_,
        );
        crate::leanh::lean_dec_ref(v___x_3031_);
        return v___x_3035_;
    } else {
        crate::leanh::lean_dec_ref(v_x_3020_);
        return v___x_3027_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___lam__0___boxed(
    mut v_body_3036_: *mut crate::leanh::LeanObject,
    mut v_unit_3037_: *mut crate::leanh::LeanObject,
    mut v_x_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
    mut v___y_3040_: *mut crate::leanh::LeanObject,
    mut v___y_3041_: *mut crate::leanh::LeanObject,
    mut v___y_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3044_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___lam__0(
        v_body_3036_,
        v_unit_3037_,
        v_x_3038_,
        v___y_3039_,
        v___y_3040_,
        v___y_3041_,
        v___y_3042_,
    );
    crate::leanh::lean_dec(v___y_3042_);
    crate::leanh::lean_dec_ref(v___y_3041_);
    crate::leanh::lean_dec(v___y_3040_);
    crate::leanh::lean_dec_ref(v___y_3039_);
    crate::leanh::lean_dec_ref(v_body_3036_);
    return v_res_3044_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit(
    mut v_type_3045_: *mut crate::leanh::LeanObject,
    mut v_unit_3046_: *mut crate::leanh::LeanObject,
    mut v_a_3047_: *mut crate::leanh::LeanObject,
    mut v_a_3048_: *mut crate::leanh::LeanObject,
    mut v_a_3049_: *mut crate::leanh::LeanObject,
    mut v_a_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_type_3045_) == 7 {
        let mut v_binderName_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3055_: u8 = 0;
        let mut v___f_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3057_: u8 = 0;
        let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_3052_ = crate::leanh::lean_ctor_get(v_type_3045_, 0);
        crate::leanh::lean_inc(v_binderName_3052_);
        v_binderType_3053_ = crate::leanh::lean_ctor_get(v_type_3045_, 1);
        crate::leanh::lean_inc_ref(v_binderType_3053_);
        v_body_3054_ = crate::leanh::lean_ctor_get(v_type_3045_, 2);
        crate::leanh::lean_inc_ref(v_body_3054_);
        v_binderInfo_3055_ = crate::leanh::lean_ctor_get_uint8(
            v_type_3045_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_type_3045_, 3);
        v___f_3056_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___lam__0___boxed
                as *mut core::ffi::c_void,
            8,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3056_, 0, v_body_3054_);
        crate::leanh::lean_closure_set(v___f_3056_, 1, v_unit_3046_);
        v___x_3057_ = 0;
        v___x_3058_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_binderName_3052_, v_binderInfo_3055_, v_binderType_3053_, v___f_3056_, v___x_3057_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
        return v___x_3058_;
    } else {
        let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_type_3045_);
        v___x_3059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3059_, 0, v_unit_3046_);
        return v___x_3059_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit___boxed(
    mut v_type_3060_: *mut crate::leanh::LeanObject,
    mut v_unit_3061_: *mut crate::leanh::LeanObject,
    mut v_a_3062_: *mut crate::leanh::LeanObject,
    mut v_a_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_a_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3067_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit(
        v_type_3060_,
        v_unit_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
        v_a_3065_,
    );
    crate::leanh::lean_dec(v_a_3065_);
    crate::leanh::lean_dec_ref(v_a_3064_);
    crate::leanh::lean_dec(v_a_3063_);
    crate::leanh::lean_dec_ref(v_a_3062_);
    return v_res_3067_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___lam__0(
    mut v_body_3068_: *mut crate::leanh::LeanObject,
    mut v_unit_3069_: *mut crate::leanh::LeanObject,
    mut v_x_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
    mut v___y_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3076_ = lean_expr_instantiate1(v_body_3068_, v_x_3070_);
    v___x_3077_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit(
        v___x_3076_,
        v_unit_3069_,
        v___y_3071_,
        v___y_3072_,
        v___y_3073_,
        v___y_3074_,
    );
    if crate::leanh::lean_obj_tag(v___x_3077_) == 0 {
        let mut v_a_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3082_: u8 = 0;
        let mut v___x_3083_: u8 = 0;
        let mut v___x_3084_: u8 = 0;
        let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3078_ = crate::leanh::lean_ctor_get(v___x_3077_, 0);
        crate::leanh::lean_inc(v_a_3078_);
        crate::leanh::lean_dec_ref_known(v___x_3077_, 1);
        v___x_3079_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3080_ = lean_mk_empty_array_with_capacity(v___x_3079_);
        v___x_3081_ = lean_array_push(v___x_3080_, v_x_3070_);
        v___x_3082_ = 0;
        v___x_3083_ = 1;
        v___x_3084_ = 1;
        v___x_3085_ = l_Lean_Meta_mkLambdaFVars(
            v___x_3081_,
            v_a_3078_,
            v___x_3082_,
            v___x_3083_,
            v___x_3082_,
            v___x_3083_,
            v___x_3084_,
            v___y_3071_,
            v___y_3072_,
            v___y_3073_,
            v___y_3074_,
        );
        crate::leanh::lean_dec_ref(v___x_3081_);
        return v___x_3085_;
    } else {
        crate::leanh::lean_dec_ref(v_x_3070_);
        return v___x_3077_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___lam__0___boxed(
    mut v_body_3086_: *mut crate::leanh::LeanObject,
    mut v_unit_3087_: *mut crate::leanh::LeanObject,
    mut v_x_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3094_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___lam__0(
            v_body_3086_,
            v_unit_3087_,
            v_x_3088_,
            v___y_3089_,
            v___y_3090_,
            v___y_3091_,
            v___y_3092_,
        );
    crate::leanh::lean_dec(v___y_3092_);
    crate::leanh::lean_dec_ref(v___y_3091_);
    crate::leanh::lean_dec(v___y_3090_);
    crate::leanh::lean_dec_ref(v___y_3089_);
    crate::leanh::lean_dec_ref(v_body_3086_);
    return v_res_3094_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit(
    mut v_type_3095_: *mut crate::leanh::LeanObject,
    mut v_unit_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
    mut v_a_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
    mut v_a_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_type_3095_) == 7 {
        let mut v_binderName_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3105_: u8 = 0;
        let mut v___f_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3107_: u8 = 0;
        let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_3102_ = crate::leanh::lean_ctor_get(v_type_3095_, 0);
        crate::leanh::lean_inc(v_binderName_3102_);
        v_binderType_3103_ = crate::leanh::lean_ctor_get(v_type_3095_, 1);
        crate::leanh::lean_inc_ref(v_binderType_3103_);
        v_body_3104_ = crate::leanh::lean_ctor_get(v_type_3095_, 2);
        crate::leanh::lean_inc_ref(v_body_3104_);
        v_binderInfo_3105_ = crate::leanh::lean_ctor_get_uint8(
            v_type_3095_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_type_3095_, 3);
        v___f_3106_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
        crate::leanh::lean_closure_set(v___f_3106_, 0, v_body_3104_);
        crate::leanh::lean_closure_set(v___f_3106_, 1, v_unit_3096_);
        v___x_3107_ = 0;
        v___x_3108_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_binderName_3102_, v_binderInfo_3105_, v_binderType_3103_, v___f_3106_, v___x_3107_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
        return v___x_3108_;
    } else {
        let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_type_3095_);
        v___x_3109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3109_, 0, v_unit_3096_);
        return v___x_3109_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit___boxed(
    mut v_type_3110_: *mut crate::leanh::LeanObject,
    mut v_unit_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
    mut v_a_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3117_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit(
        v_type_3110_,
        v_unit_3111_,
        v_a_3112_,
        v_a_3113_,
        v_a_3114_,
        v_a_3115_,
    );
    crate::leanh::lean_dec(v_a_3115_);
    crate::leanh::lean_dec_ref(v_a_3114_);
    crate::leanh::lean_dec(v_a_3113_);
    crate::leanh::lean_dec_ref(v_a_3112_);
    return v_res_3117_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_forallBody(
    mut v_type_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_body_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_type_3118_) == 7 {
                    v_body_3119_ = crate::leanh::lean_ctor_get(v_type_3118_, 2);
                    v_type_3118_ = v_body_3119_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_type_3118_);
                    return v_type_3118_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_forallBody___boxed(
    mut v_type_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3122_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_forallBody(v_type_3121_);
    crate::leanh::lean_dec_ref(v_type_3121_);
    return v_res_3122_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0_spec__0(
    mut v_a_3123_: *mut crate::leanh::LeanObject,
    mut v_as_3124_: *mut crate::leanh::LeanObject,
    mut v_i_3125_: usize,
    mut v_stop_3126_: usize,
) -> u8 {
    let mut v___x_3127_: u8 = 0;
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3130_: usize = 0;
    let mut v___x_3131_: usize = 0;
    let mut v___x_3133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3127_ = lean_usize_dec_eq(v_i_3125_, v_stop_3126_);
                if v___x_3127_ == 0 {
                    v___x_3128_ = lean_array_uget_borrowed(v_as_3124_, v_i_3125_);
                    v___x_3129_ = l_Lean_instBEqFVarId_beq(v_a_3123_, v___x_3128_);
                    if v___x_3129_ == 0 {
                        v___x_3130_ = 1usize;
                        v___x_3131_ = lean_usize_add(v_i_3125_, v___x_3130_);
                        v_i_3125_ = v___x_3131_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3129_;
                    }
                } else {
                    v___x_3133_ = 0;
                    return v___x_3133_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0_spec__0___boxed(
    mut v_a_3134_: *mut crate::leanh::LeanObject,
    mut v_as_3135_: *mut crate::leanh::LeanObject,
    mut v_i_3136_: *mut crate::leanh::LeanObject,
    mut v_stop_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3138_: usize = 0;
    let mut v_stop_boxed_3139_: usize = 0;
    let mut v_res_3140_: u8 = 0;
    let mut v_r_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3138_ = crate::leanh::lean_unbox_usize(v_i_3136_);
    crate::leanh::lean_dec(v_i_3136_);
    v_stop_boxed_3139_ = crate::leanh::lean_unbox_usize(v_stop_3137_);
    crate::leanh::lean_dec(v_stop_3137_);
    v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0_spec__0(v_a_3134_, v_as_3135_, v_i_boxed_3138_, v_stop_boxed_3139_);
    crate::leanh::lean_dec_ref(v_as_3135_);
    crate::leanh::lean_dec(v_a_3134_);
    v_r_3141_ = crate::leanh::lean_box((v_res_3140_) as usize);
    return v_r_3141_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0(
    mut v_as_3142_: *mut crate::leanh::LeanObject,
    mut v_a_3143_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: u8 = 0;
    v___x_3144_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3145_ = lean_array_get_size(v_as_3142_);
    v___x_3146_ = lean_nat_dec_lt(v___x_3144_, v___x_3145_);
    if v___x_3146_ == 0 {
        return v___x_3146_;
    } else {
        if v___x_3146_ == 0 {
            return v___x_3146_;
        } else {
            let mut v___x_3147_: usize = 0;
            let mut v___x_3148_: usize = 0;
            let mut v___x_3149_: u8 = 0;
            v___x_3147_ = 0usize;
            v___x_3148_ = lean_usize_of_nat(v___x_3145_);
            v___x_3149_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0_spec__0(v_a_3143_, v_as_3142_, v___x_3147_, v___x_3148_);
            return v___x_3149_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0___boxed(
    mut v_as_3150_: *mut crate::leanh::LeanObject,
    mut v_a_3151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3152_: u8 = 0;
    let mut v_r_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0(v_as_3150_, v_a_3151_);
    crate::leanh::lean_dec(v_a_3151_);
    crate::leanh::lean_dec_ref(v_as_3150_);
    v_r_3153_ = crate::leanh::lean_box((v_res_3152_) as usize);
    return v_r_3153_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg(
    mut v_motiveIds_3154_: *mut crate::leanh::LeanObject,
    mut v_arg_3155_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_Expr_getAppFn(v_arg_3155_);
    if crate::leanh::lean_obj_tag(v___x_3156_) == 1 {
        let mut v_fvarId_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3158_: u8 = 0;
        v_fvarId_3157_ = crate::leanh::lean_ctor_get(v___x_3156_, 0);
        crate::leanh::lean_inc(v_fvarId_3157_);
        crate::leanh::lean_dec_ref_known(v___x_3156_, 1);
        v___x_3158_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg_spec__0(v_motiveIds_3154_, v_fvarId_3157_);
        crate::leanh::lean_dec(v_fvarId_3157_);
        return v___x_3158_;
    } else {
        let mut v___x_3159_: u8 = 0;
        crate::leanh::lean_dec_ref(v___x_3156_);
        v___x_3159_ = 0;
        return v___x_3159_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg___boxed(
    mut v_motiveIds_3160_: *mut crate::leanh::LeanObject,
    mut v_arg_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3162_: u8 = 0;
    let mut v_r_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3162_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg(
        v_motiveIds_3160_,
        v_arg_3161_,
    );
    crate::leanh::lean_dec_ref(v_arg_3161_);
    crate::leanh::lean_dec_ref(v_motiveIds_3160_);
    v_r_3163_ = crate::leanh::lean_box((v_res_3162_) as usize);
    return v_r_3163_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__0___boxed(
    mut v_minorParams_3164_: *mut crate::leanh::LeanObject,
    mut v_motiveIds_3165_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3166_: *mut crate::leanh::LeanObject,
    mut v_unit_3167_: *mut crate::leanh::LeanObject,
    mut v_body_3168_: *mut crate::leanh::LeanObject,
    mut v_isMain_3169_: *mut crate::leanh::LeanObject,
    mut v_minorNonRecParams_3170_: *mut crate::leanh::LeanObject,
    mut v_k_3171_: *mut crate::leanh::LeanObject,
    mut v_newLocal_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMain_boxed_3178_: u8 = 0;
    let mut v_res_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMain_boxed_3178_ = (crate::leanh::lean_unbox(v_isMain_3169_) as u8);
    v_res_3179_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__0(
            v_minorParams_3164_,
            v_motiveIds_3165_,
            v_mainMotiveId_3166_,
            v_unit_3167_,
            v_body_3168_,
            v_isMain_boxed_3178_,
            v_minorNonRecParams_3170_,
            v_k_3171_,
            v_newLocal_3172_,
            v___y_3173_,
            v___y_3174_,
            v___y_3175_,
            v___y_3176_,
        );
    crate::leanh::lean_dec(v___y_3176_);
    crate::leanh::lean_dec_ref(v___y_3175_);
    crate::leanh::lean_dec(v___y_3174_);
    crate::leanh::lean_dec_ref(v___y_3173_);
    return v_res_3179_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__1(
    mut v_body_3180_: *mut crate::leanh::LeanObject,
    mut v_binderType_3181_: *mut crate::leanh::LeanObject,
    mut v_motiveIds_3182_: *mut crate::leanh::LeanObject,
    mut v_minorParams_3183_: *mut crate::leanh::LeanObject,
    mut v_isMain_3184_: u8,
    mut v_mainMotiveId_3185_: *mut crate::leanh::LeanObject,
    mut v_unit_3186_: *mut crate::leanh::LeanObject,
    mut v_minorNonRecParams_3187_: *mut crate::leanh::LeanObject,
    mut v_k_3188_: *mut crate::leanh::LeanObject,
    mut v_binderName_3189_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_3190_: u8,
    mut v_x_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_body_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_argTarget_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: u8 = 0;
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_body_3197_ = lean_expr_instantiate1(v_body_3180_, v_x_3191_);
                v_argTarget_3198_ =
                    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_forallBody(
                        v_binderType_3181_,
                    );
                v___x_3199_ =
                    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_isTypeFormerArg(
                        v_motiveIds_3182_,
                        v_argTarget_3198_,
                    );
                if v___x_3199_ == 0 {
                    crate::leanh::lean_dec_ref(v_argTarget_3198_);
                    crate::leanh::lean_dec(v_binderName_3189_);
                    crate::leanh::lean_dec_ref(v_binderType_3181_);
                    crate::leanh::lean_inc_ref(v_x_3191_);
                    v___x_3200_ = lean_array_push(v_minorParams_3183_, v_x_3191_);
                    if v_isMain_3184_ == 0 {
                        crate::leanh::lean_dec_ref(v_x_3191_);
                        v___x_3201_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(v_motiveIds_3182_, v_mainMotiveId_3185_, v_unit_3186_, v_body_3197_, v_isMain_3184_, v___x_3200_, v_minorNonRecParams_3187_, v_k_3188_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
                        return v___x_3201_;
                    } else {
                        v___x_3202_ = lean_array_push(v_minorNonRecParams_3187_, v_x_3191_);
                        v___x_3203_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(v_motiveIds_3182_, v_mainMotiveId_3185_, v_unit_3186_, v_body_3197_, v_isMain_3184_, v___x_3200_, v___x_3202_, v_k_3188_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
                        return v___x_3203_;
                    }
                } else {
                    v___x_3204_ = l_Lean_Expr_getAppFn(v_argTarget_3198_);
                    crate::leanh::lean_dec_ref(v_argTarget_3198_);
                    v___x_3205_ = l_Lean_Expr_fvarId_x21(v___x_3204_);
                    crate::leanh::lean_dec_ref(v___x_3204_);
                    v___x_3206_ = l_Lean_instBEqFVarId_beq(v___x_3205_, v_mainMotiveId_3185_);
                    crate::leanh::lean_dec(v___x_3205_);
                    if v___x_3206_ == 0 {
                        crate::leanh::lean_dec_ref(v_x_3191_);
                        crate::leanh::lean_inc_ref(v_unit_3186_);
                        v___x_3207_ =
                            l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit(
                                v_binderType_3181_,
                                v_unit_3186_,
                                v___y_3192_,
                                v___y_3193_,
                                v___y_3194_,
                                v___y_3195_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3207_) == 0 {
                            v_a_3208_ = crate::leanh::lean_ctor_get(v___x_3207_, 0);
                            crate::leanh::lean_inc(v_a_3208_);
                            crate::leanh::lean_dec_ref_known(v___x_3207_, 1);
                            v___x_3209_ = crate::leanh::lean_box((v_isMain_3184_) as usize);
                            v___f_3210_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 8);
                            crate::leanh::lean_closure_set(v___f_3210_, 0, v_minorParams_3183_);
                            crate::leanh::lean_closure_set(v___f_3210_, 1, v_motiveIds_3182_);
                            crate::leanh::lean_closure_set(v___f_3210_, 2, v_mainMotiveId_3185_);
                            crate::leanh::lean_closure_set(v___f_3210_, 3, v_unit_3186_);
                            crate::leanh::lean_closure_set(v___f_3210_, 4, v_body_3197_);
                            crate::leanh::lean_closure_set(v___f_3210_, 5, v___x_3209_);
                            crate::leanh::lean_closure_set(
                                v___f_3210_,
                                6,
                                v_minorNonRecParams_3187_,
                            );
                            crate::leanh::lean_closure_set(v___f_3210_, 7, v_k_3188_);
                            v___x_3211_ = 0;
                            v___x_3212_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_binderName_3189_, v_binderInfo_3190_, v_a_3208_, v___f_3210_, v___x_3211_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
                            return v___x_3212_;
                        } else {
                            crate::leanh::lean_dec_ref(v_body_3197_);
                            crate::leanh::lean_dec(v_binderName_3189_);
                            crate::leanh::lean_dec_ref(v_k_3188_);
                            crate::leanh::lean_dec_ref(v_minorNonRecParams_3187_);
                            crate::leanh::lean_dec_ref(v_unit_3186_);
                            crate::leanh::lean_dec(v_mainMotiveId_3185_);
                            crate::leanh::lean_dec_ref(v_minorParams_3183_);
                            crate::leanh::lean_dec_ref(v_motiveIds_3182_);
                            v_a_3213_ = crate::leanh::lean_ctor_get(v___x_3207_, 0);
                            v_isSharedCheck_3220_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3207_)) as u8;
                            if v_isSharedCheck_3220_ == 0 {
                                v___x_3215_ = v___x_3207_;
                                v_isShared_3216_ = v_isSharedCheck_3220_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3213_);
                                crate::leanh::lean_dec(v___x_3207_);
                                v___x_3215_ = crate::leanh::lean_box(0);
                                v_isShared_3216_ = v_isSharedCheck_3220_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_3189_);
                        crate::leanh::lean_dec_ref(v_binderType_3181_);
                        v___x_3221_ = lean_array_push(v_minorParams_3183_, v_x_3191_);
                        v___x_3222_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(v_motiveIds_3182_, v_mainMotiveId_3185_, v_unit_3186_, v_body_3197_, v_isMain_3184_, v___x_3221_, v_minorNonRecParams_3187_, v_k_3188_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
                        return v___x_3222_;
                    }
                }
            }
            1 => {
                if v_isShared_3216_ == 0 {
                    v___x_3218_ = v___x_3215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
                    v___x_3218_ = v_reuseFailAlloc_3219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_body_3223_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_binderType_3224_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_motiveIds_3225_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_minorParams_3226_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_isMain_3227_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_mainMotiveId_3228_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_unit_3229_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_minorNonRecParams_3230_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_k_3231_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_binderName_3232_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_binderInfo_3233_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_x_3234_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3235_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3236_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3237_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3238_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3239_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_isMain_boxed_3240_: u8 = 0;
    let mut v_binderInfo_548__boxed_3241_: u8 = 0;
    let mut v_res_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMain_boxed_3240_ = (crate::leanh::lean_unbox(v_isMain_3227_) as u8);
    v_binderInfo_548__boxed_3241_ = (crate::leanh::lean_unbox(v_binderInfo_3233_) as u8);
    v_res_3242_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__1(
            v_body_3223_,
            v_binderType_3224_,
            v_motiveIds_3225_,
            v_minorParams_3226_,
            v_isMain_boxed_3240_,
            v_mainMotiveId_3228_,
            v_unit_3229_,
            v_minorNonRecParams_3230_,
            v_k_3231_,
            v_binderName_3232_,
            v_binderInfo_548__boxed_3241_,
            v_x_3234_,
            v___y_3235_,
            v___y_3236_,
            v___y_3237_,
            v___y_3238_,
        );
    crate::leanh::lean_dec(v___y_3238_);
    crate::leanh::lean_dec_ref(v___y_3237_);
    crate::leanh::lean_dec(v___y_3236_);
    crate::leanh::lean_dec_ref(v___y_3235_);
    crate::leanh::lean_dec_ref(v_body_3223_);
    return v_res_3242_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(
    mut v_motiveIds_3243_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3244_: *mut crate::leanh::LeanObject,
    mut v_unit_3245_: *mut crate::leanh::LeanObject,
    mut v_minorType_3246_: *mut crate::leanh::LeanObject,
    mut v_isMain_3247_: u8,
    mut v_minorParams_3248_: *mut crate::leanh::LeanObject,
    mut v_minorNonRecParams_3249_: *mut crate::leanh::LeanObject,
    mut v_k_3250_: *mut crate::leanh::LeanObject,
    mut v_a_3251_: *mut crate::leanh::LeanObject,
    mut v_a_3252_: *mut crate::leanh::LeanObject,
    mut v_a_3253_: *mut crate::leanh::LeanObject,
    mut v_a_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_minorType_3246_) == 7 {
        let mut v_binderName_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3259_: u8 = 0;
        let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3263_: u8 = 0;
        let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_3256_ = crate::leanh::lean_ctor_get(v_minorType_3246_, 0);
        crate::leanh::lean_inc_n(v_binderName_3256_, 2);
        v_binderType_3257_ = crate::leanh::lean_ctor_get(v_minorType_3246_, 1);
        crate::leanh::lean_inc_ref_n(v_binderType_3257_, 2);
        v_body_3258_ = crate::leanh::lean_ctor_get(v_minorType_3246_, 2);
        crate::leanh::lean_inc_ref(v_body_3258_);
        v_binderInfo_3259_ = crate::leanh::lean_ctor_get_uint8(
            v_minorType_3246_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_minorType_3246_, 3);
        v___x_3260_ = crate::leanh::lean_box((v_isMain_3247_) as usize);
        v___x_3261_ = crate::leanh::lean_box((v_binderInfo_3259_) as usize);
        v___f_3262_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__1___boxed as *mut core::ffi::c_void, 17, 11);
        crate::leanh::lean_closure_set(v___f_3262_, 0, v_body_3258_);
        crate::leanh::lean_closure_set(v___f_3262_, 1, v_binderType_3257_);
        crate::leanh::lean_closure_set(v___f_3262_, 2, v_motiveIds_3243_);
        crate::leanh::lean_closure_set(v___f_3262_, 3, v_minorParams_3248_);
        crate::leanh::lean_closure_set(v___f_3262_, 4, v___x_3260_);
        crate::leanh::lean_closure_set(v___f_3262_, 5, v_mainMotiveId_3244_);
        crate::leanh::lean_closure_set(v___f_3262_, 6, v_unit_3245_);
        crate::leanh::lean_closure_set(v___f_3262_, 7, v_minorNonRecParams_3249_);
        crate::leanh::lean_closure_set(v___f_3262_, 8, v_k_3250_);
        crate::leanh::lean_closure_set(v___f_3262_, 9, v_binderName_3256_);
        crate::leanh::lean_closure_set(v___f_3262_, 10, v___x_3261_);
        v___x_3263_ = 0;
        v___x_3264_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v_binderName_3256_, v_binderInfo_3259_, v_binderType_3257_, v___f_3262_, v___x_3263_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
        return v___x_3264_;
    } else {
        let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_unit_3245_);
        crate::leanh::lean_dec(v_mainMotiveId_3244_);
        crate::leanh::lean_dec_ref(v_motiveIds_3243_);
        crate::leanh::lean_inc(v_a_3254_);
        crate::leanh::lean_inc_ref(v_a_3253_);
        crate::leanh::lean_inc(v_a_3252_);
        crate::leanh::lean_inc_ref(v_a_3251_);
        v___x_3265_ = crate::leanh::lean_apply_8(
            v_k_3250_,
            v_minorParams_3248_,
            v_minorNonRecParams_3249_,
            v_minorType_3246_,
            v_a_3251_,
            v_a_3252_,
            v_a_3253_,
            v_a_3254_,
            crate::leanh::lean_box(0),
        );
        return v___x_3265_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___lam__0(
    mut v_minorParams_3266_: *mut crate::leanh::LeanObject,
    mut v_motiveIds_3267_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3268_: *mut crate::leanh::LeanObject,
    mut v_unit_3269_: *mut crate::leanh::LeanObject,
    mut v_body_3270_: *mut crate::leanh::LeanObject,
    mut v_isMain_3271_: u8,
    mut v_minorNonRecParams_3272_: *mut crate::leanh::LeanObject,
    mut v_k_3273_: *mut crate::leanh::LeanObject,
    mut v_newLocal_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
    mut v___y_3276_: *mut crate::leanh::LeanObject,
    mut v___y_3277_: *mut crate::leanh::LeanObject,
    mut v___y_3278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3280_ = lean_array_push(v_minorParams_3266_, v_newLocal_3274_);
    v___x_3281_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(
        v_motiveIds_3267_,
        v_mainMotiveId_3268_,
        v_unit_3269_,
        v_body_3270_,
        v_isMain_3271_,
        v___x_3280_,
        v_minorNonRecParams_3272_,
        v_k_3273_,
        v___y_3275_,
        v___y_3276_,
        v___y_3277_,
        v___y_3278_,
    );
    return v___x_3281_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg___boxed(
    mut v_motiveIds_3282_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3283_: *mut crate::leanh::LeanObject,
    mut v_unit_3284_: *mut crate::leanh::LeanObject,
    mut v_minorType_3285_: *mut crate::leanh::LeanObject,
    mut v_isMain_3286_: *mut crate::leanh::LeanObject,
    mut v_minorParams_3287_: *mut crate::leanh::LeanObject,
    mut v_minorNonRecParams_3288_: *mut crate::leanh::LeanObject,
    mut v_k_3289_: *mut crate::leanh::LeanObject,
    mut v_a_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
    mut v_a_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMain_boxed_3295_: u8 = 0;
    let mut v_res_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMain_boxed_3295_ = (crate::leanh::lean_unbox(v_isMain_3286_) as u8);
    v_res_3296_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(
        v_motiveIds_3282_,
        v_mainMotiveId_3283_,
        v_unit_3284_,
        v_minorType_3285_,
        v_isMain_boxed_3295_,
        v_minorParams_3287_,
        v_minorNonRecParams_3288_,
        v_k_3289_,
        v_a_3290_,
        v_a_3291_,
        v_a_3292_,
        v_a_3293_,
    );
    crate::leanh::lean_dec(v_a_3293_);
    crate::leanh::lean_dec_ref(v_a_3292_);
    crate::leanh::lean_dec(v_a_3291_);
    crate::leanh::lean_dec_ref(v_a_3290_);
    return v_res_3296_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams(
    mut v_00_u03b1_3297_: *mut crate::leanh::LeanObject,
    mut v_motiveIds_3298_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3299_: *mut crate::leanh::LeanObject,
    mut v_unit_3300_: *mut crate::leanh::LeanObject,
    mut v_minorType_3301_: *mut crate::leanh::LeanObject,
    mut v_isMain_3302_: u8,
    mut v_minorParams_3303_: *mut crate::leanh::LeanObject,
    mut v_minorNonRecParams_3304_: *mut crate::leanh::LeanObject,
    mut v_k_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(
        v_motiveIds_3298_,
        v_mainMotiveId_3299_,
        v_unit_3300_,
        v_minorType_3301_,
        v_isMain_3302_,
        v_minorParams_3303_,
        v_minorNonRecParams_3304_,
        v_k_3305_,
        v_a_3306_,
        v_a_3307_,
        v_a_3308_,
        v_a_3309_,
    );
    return v___x_3311_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___boxed(
    mut v_00_u03b1_3312_: *mut crate::leanh::LeanObject,
    mut v_motiveIds_3313_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3314_: *mut crate::leanh::LeanObject,
    mut v_unit_3315_: *mut crate::leanh::LeanObject,
    mut v_minorType_3316_: *mut crate::leanh::LeanObject,
    mut v_isMain_3317_: *mut crate::leanh::LeanObject,
    mut v_minorParams_3318_: *mut crate::leanh::LeanObject,
    mut v_minorNonRecParams_3319_: *mut crate::leanh::LeanObject,
    mut v_k_3320_: *mut crate::leanh::LeanObject,
    mut v_a_3321_: *mut crate::leanh::LeanObject,
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_a_3323_: *mut crate::leanh::LeanObject,
    mut v_a_3324_: *mut crate::leanh::LeanObject,
    mut v_a_3325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMain_boxed_3326_: u8 = 0;
    let mut v_res_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMain_boxed_3326_ = (crate::leanh::lean_unbox(v_isMain_3317_) as u8);
    v_res_3327_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams(
        v_00_u03b1_3312_,
        v_motiveIds_3313_,
        v_mainMotiveId_3314_,
        v_unit_3315_,
        v_minorType_3316_,
        v_isMain_boxed_3326_,
        v_minorParams_3318_,
        v_minorNonRecParams_3319_,
        v_k_3320_,
        v_a_3321_,
        v_a_3322_,
        v_a_3323_,
        v_a_3324_,
    );
    crate::leanh::lean_dec(v_a_3324_);
    crate::leanh::lean_dec_ref(v_a_3323_);
    crate::leanh::lean_dec(v_a_3322_);
    crate::leanh::lean_dec_ref(v_a_3321_);
    return v_res_3327_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_minorNonRecParams_3328_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_minorParams_3329_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_3330_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3331_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3332_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_minorIdx_3333_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_casesOnParams_3334_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_recArgs_3335_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_motiveIds_3336_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_mainMotiveId_3337_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_unit_3338_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_star_3339_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_minorEntries_3340_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_k_3341_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_newC_3342_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3343_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3344_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3345_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_3346_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_3347_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_799__boxed_3348_: u8 = 0;
    let mut v___x_800__boxed_3349_: u8 = 0;
    let mut v___x_801__boxed_3350_: u8 = 0;
    let mut v_res_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_799__boxed_3348_ = (crate::leanh::lean_unbox(v___x_3330_) as u8);
    v___x_800__boxed_3349_ = (crate::leanh::lean_unbox(v___x_3331_) as u8);
    v___x_801__boxed_3350_ = (crate::leanh::lean_unbox(v___x_3332_) as u8);
    v_res_3351_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__0(
            v_minorNonRecParams_3328_,
            v_minorParams_3329_,
            v___x_799__boxed_3348_,
            v___x_800__boxed_3349_,
            v___x_801__boxed_3350_,
            v_minorIdx_3333_,
            v_casesOnParams_3334_,
            v_recArgs_3335_,
            v_motiveIds_3336_,
            v_mainMotiveId_3337_,
            v_unit_3338_,
            v_star_3339_,
            v_minorEntries_3340_,
            v_k_3341_,
            v_newC_3342_,
            v___y_3343_,
            v___y_3344_,
            v___y_3345_,
            v___y_3346_,
        );
    crate::leanh::lean_dec(v___y_3346_);
    crate::leanh::lean_dec_ref(v___y_3345_);
    crate::leanh::lean_dec(v___y_3344_);
    crate::leanh::lean_dec_ref(v___y_3343_);
    crate::leanh::lean_dec(v_minorIdx_3333_);
    crate::leanh::lean_dec_ref(v_minorParams_3329_);
    crate::leanh::lean_dec_ref(v_minorNonRecParams_3328_);
    return v_res_3351_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__1(
    mut v_snd_3352_: u8,
    mut v_star_3353_: *mut crate::leanh::LeanObject,
    mut v___x_3354_: u8,
    mut v_minorIdx_3355_: *mut crate::leanh::LeanObject,
    mut v_recArgs_3356_: *mut crate::leanh::LeanObject,
    mut v_motiveIds_3357_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3358_: *mut crate::leanh::LeanObject,
    mut v_unit_3359_: *mut crate::leanh::LeanObject,
    mut v_minorEntries_3360_: *mut crate::leanh::LeanObject,
    mut v_casesOnParams_3361_: *mut crate::leanh::LeanObject,
    mut v_k_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
    mut v_minorParams_3364_: *mut crate::leanh::LeanObject,
    mut v_minorNonRecParams_3365_: *mut crate::leanh::LeanObject,
    mut v_minorType_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v___x_3387_: u8 = 0;
    let mut v___x_3388_: u8 = 0;
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3402_: u8 = 0;
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_snd_3352_ == 0 {
                    crate::leanh::lean_dec_ref(v_minorType_3366_);
                    crate::leanh::lean_dec_ref(v_minorNonRecParams_3365_);
                    v___x_3372_ = 1;
                    crate::leanh::lean_inc_ref(v_star_3353_);
                    v___x_3373_ = l_Lean_Meta_mkLambdaFVars(
                        v_minorParams_3364_,
                        v_star_3353_,
                        v_snd_3352_,
                        v___x_3354_,
                        v_snd_3352_,
                        v___x_3354_,
                        v___x_3372_,
                        v___y_3367_,
                        v___y_3368_,
                        v___y_3369_,
                        v___y_3370_,
                    );
                    crate::leanh::lean_dec_ref(v_minorParams_3364_);
                    if crate::leanh::lean_obj_tag(v___x_3373_) == 0 {
                        v_a_3374_ = crate::leanh::lean_ctor_get(v___x_3373_, 0);
                        crate::leanh::lean_inc(v_a_3374_);
                        crate::leanh::lean_dec_ref_known(v___x_3373_, 1);
                        v___x_3375_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3376_ = lean_nat_add(v_minorIdx_3355_, v___x_3375_);
                        crate::leanh::lean_dec(v_minorIdx_3355_);
                        v___x_3377_ = lean_array_push(v_recArgs_3356_, v_a_3374_);
                        v___x_3378_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(v_motiveIds_3357_, v_mainMotiveId_3358_, v_unit_3359_, v_star_3353_, v_minorEntries_3360_, v___x_3376_, v_casesOnParams_3361_, v___x_3377_, v_k_3362_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
                        return v___x_3378_;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_3362_);
                        crate::leanh::lean_dec_ref(v_casesOnParams_3361_);
                        crate::leanh::lean_dec_ref(v_minorEntries_3360_);
                        crate::leanh::lean_dec_ref(v_unit_3359_);
                        crate::leanh::lean_dec(v_mainMotiveId_3358_);
                        crate::leanh::lean_dec_ref(v_motiveIds_3357_);
                        crate::leanh::lean_dec_ref(v_recArgs_3356_);
                        crate::leanh::lean_dec(v_minorIdx_3355_);
                        crate::leanh::lean_dec_ref(v_star_3353_);
                        v_a_3379_ = crate::leanh::lean_ctor_get(v___x_3373_, 0);
                        v_isSharedCheck_3386_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3373_)) as u8;
                        if v_isSharedCheck_3386_ == 0 {
                            v___x_3381_ = v___x_3373_;
                            v_isShared_3382_ = v_isSharedCheck_3386_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3379_);
                            crate::leanh::lean_dec(v___x_3373_);
                            v___x_3381_ = crate::leanh::lean_box(0);
                            v_isShared_3382_ = v_isSharedCheck_3386_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3387_ = 0;
                    v___x_3388_ = 1;
                    v___x_3389_ = l_Lean_Meta_mkForallFVars(
                        v_minorNonRecParams_3365_,
                        v_minorType_3366_,
                        v___x_3387_,
                        v___x_3354_,
                        v___x_3354_,
                        v___x_3388_,
                        v___y_3367_,
                        v___y_3368_,
                        v___y_3369_,
                        v___y_3370_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3389_) == 0 {
                        v_a_3390_ = crate::leanh::lean_ctor_get(v___x_3389_, 0);
                        crate::leanh::lean_inc(v_a_3390_);
                        crate::leanh::lean_dec_ref_known(v___x_3389_, 1);
                        v___x_3391_ = crate::leanh::lean_box((v___x_3387_) as usize);
                        v___x_3392_ = crate::leanh::lean_box((v___x_3354_) as usize);
                        v___x_3393_ = crate::leanh::lean_box((v___x_3388_) as usize);
                        v___f_3394_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__0___boxed as *mut core::ffi::c_void, 20, 14);
                        crate::leanh::lean_closure_set(v___f_3394_, 0, v_minorNonRecParams_3365_);
                        crate::leanh::lean_closure_set(v___f_3394_, 1, v_minorParams_3364_);
                        crate::leanh::lean_closure_set(v___f_3394_, 2, v___x_3391_);
                        crate::leanh::lean_closure_set(v___f_3394_, 3, v___x_3392_);
                        crate::leanh::lean_closure_set(v___f_3394_, 4, v___x_3393_);
                        crate::leanh::lean_closure_set(v___f_3394_, 5, v_minorIdx_3355_);
                        crate::leanh::lean_closure_set(v___f_3394_, 6, v_casesOnParams_3361_);
                        crate::leanh::lean_closure_set(v___f_3394_, 7, v_recArgs_3356_);
                        crate::leanh::lean_closure_set(v___f_3394_, 8, v_motiveIds_3357_);
                        crate::leanh::lean_closure_set(v___f_3394_, 9, v_mainMotiveId_3358_);
                        crate::leanh::lean_closure_set(v___f_3394_, 10, v_unit_3359_);
                        crate::leanh::lean_closure_set(v___f_3394_, 11, v_star_3353_);
                        crate::leanh::lean_closure_set(v___f_3394_, 12, v_minorEntries_3360_);
                        crate::leanh::lean_closure_set(v___f_3394_, 13, v_k_3362_);
                        v___x_3395_ = l_Lean_LocalDecl_userName(v_a_3363_);
                        v___x_3396_ = l_Lean_LocalDecl_binderInfo(v_a_3363_);
                        v___x_3397_ = 0;
                        v___x_3398_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkPiUnit_spec__0___redArg(v___x_3395_, v___x_3396_, v_a_3390_, v___f_3394_, v___x_3397_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
                        return v___x_3398_;
                    } else {
                        crate::leanh::lean_dec_ref(v_minorNonRecParams_3365_);
                        crate::leanh::lean_dec_ref(v_minorParams_3364_);
                        crate::leanh::lean_dec_ref(v_k_3362_);
                        crate::leanh::lean_dec_ref(v_casesOnParams_3361_);
                        crate::leanh::lean_dec_ref(v_minorEntries_3360_);
                        crate::leanh::lean_dec_ref(v_unit_3359_);
                        crate::leanh::lean_dec(v_mainMotiveId_3358_);
                        crate::leanh::lean_dec_ref(v_motiveIds_3357_);
                        crate::leanh::lean_dec_ref(v_recArgs_3356_);
                        crate::leanh::lean_dec(v_minorIdx_3355_);
                        crate::leanh::lean_dec_ref(v_star_3353_);
                        v_a_3399_ = crate::leanh::lean_ctor_get(v___x_3389_, 0);
                        v_isSharedCheck_3406_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3389_)) as u8;
                        if v_isSharedCheck_3406_ == 0 {
                            v___x_3401_ = v___x_3389_;
                            v_isShared_3402_ = v_isSharedCheck_3406_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3399_);
                            crate::leanh::lean_dec(v___x_3389_);
                            v___x_3401_ = crate::leanh::lean_box(0);
                            v_isShared_3402_ = v_isSharedCheck_3406_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3382_ == 0 {
                    v___x_3384_ = v___x_3381_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3384_;
            }
            3 => {
                if v_isShared_3402_ == 0 {
                    v___x_3404_ = v___x_3401_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
                    v___x_3404_ = v_reuseFailAlloc_3405_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3407_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_star_3408_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_3409_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_minorIdx_3410_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_recArgs_3411_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_motiveIds_3412_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_mainMotiveId_3413_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_unit_3414_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_minorEntries_3415_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_casesOnParams_3416_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_k_3417_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3418_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_minorParams_3419_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_minorNonRecParams_3420_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_minorType_3421_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3422_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3423_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3424_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_3425_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_3426_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_snd_835__boxed_3427_: u8 = 0;
    let mut v___x_836__boxed_3428_: u8 = 0;
    let mut v_res_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_835__boxed_3427_ = (crate::leanh::lean_unbox(v_snd_3407_) as u8);
    v___x_836__boxed_3428_ = (crate::leanh::lean_unbox(v___x_3409_) as u8);
    v_res_3429_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__1(
            v_snd_835__boxed_3427_,
            v_star_3408_,
            v___x_836__boxed_3428_,
            v_minorIdx_3410_,
            v_recArgs_3411_,
            v_motiveIds_3412_,
            v_mainMotiveId_3413_,
            v_unit_3414_,
            v_minorEntries_3415_,
            v_casesOnParams_3416_,
            v_k_3417_,
            v_a_3418_,
            v_minorParams_3419_,
            v_minorNonRecParams_3420_,
            v_minorType_3421_,
            v___y_3422_,
            v___y_3423_,
            v___y_3424_,
            v___y_3425_,
        );
    crate::leanh::lean_dec(v___y_3425_);
    crate::leanh::lean_dec_ref(v___y_3424_);
    crate::leanh::lean_dec(v___y_3423_);
    crate::leanh::lean_dec_ref(v___y_3422_);
    crate::leanh::lean_dec_ref(v_a_3418_);
    return v_res_3429_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(
    mut v_motiveIds_3432_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3433_: *mut crate::leanh::LeanObject,
    mut v_unit_3434_: *mut crate::leanh::LeanObject,
    mut v_star_3435_: *mut crate::leanh::LeanObject,
    mut v_minorEntries_3436_: *mut crate::leanh::LeanObject,
    mut v_minorIdx_3437_: *mut crate::leanh::LeanObject,
    mut v_casesOnParams_3438_: *mut crate::leanh::LeanObject,
    mut v_recArgs_3439_: *mut crate::leanh::LeanObject,
    mut v_k_3440_: *mut crate::leanh::LeanObject,
    mut v_a_3441_: *mut crate::leanh::LeanObject,
    mut v_a_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: u8 = 0;
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: u8 = 0;
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3446_ = lean_array_get_size(v_minorEntries_3436_);
                v___x_3447_ = lean_nat_dec_lt(v_minorIdx_3437_, v___x_3446_);
                if v___x_3447_ == 0 {
                    crate::leanh::lean_dec(v_minorIdx_3437_);
                    crate::leanh::lean_dec_ref(v_minorEntries_3436_);
                    crate::leanh::lean_dec_ref(v_star_3435_);
                    crate::leanh::lean_dec_ref(v_unit_3434_);
                    crate::leanh::lean_dec(v_mainMotiveId_3433_);
                    crate::leanh::lean_dec_ref(v_motiveIds_3432_);
                    crate::leanh::lean_inc(v_a_3444_);
                    crate::leanh::lean_inc_ref(v_a_3443_);
                    crate::leanh::lean_inc(v_a_3442_);
                    crate::leanh::lean_inc_ref(v_a_3441_);
                    v___x_3448_ = crate::leanh::lean_apply_7(
                        v_k_3440_,
                        v_casesOnParams_3438_,
                        v_recArgs_3439_,
                        v_a_3441_,
                        v_a_3442_,
                        v_a_3443_,
                        v_a_3444_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3448_;
                } else {
                    v___x_3449_ = lean_array_fget_borrowed(v_minorEntries_3436_, v_minorIdx_3437_);
                    v_fst_3450_ = crate::leanh::lean_ctor_get(v___x_3449_, 0);
                    v_snd_3451_ = crate::leanh::lean_ctor_get(v___x_3449_, 1);
                    crate::leanh::lean_inc(v_snd_3451_);
                    v___x_3452_ = l_Lean_Expr_fvarId_x21(v_fst_3450_);
                    v___x_3453_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_3452_,
                        v_a_3441_,
                        v_a_3443_,
                        v_a_3444_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3453_) == 0 {
                        v_a_3454_ = crate::leanh::lean_ctor_get(v___x_3453_, 0);
                        crate::leanh::lean_inc_n(v_a_3454_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3453_, 1);
                        v___x_3455_ = crate::leanh::lean_box((v___x_3447_) as usize);
                        crate::leanh::lean_inc_ref(v_unit_3434_);
                        crate::leanh::lean_inc(v_mainMotiveId_3433_);
                        crate::leanh::lean_inc_ref(v_motiveIds_3432_);
                        crate::leanh::lean_inc(v_snd_3451_);
                        v___f_3456_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__1___boxed as *mut core::ffi::c_void, 20, 12);
                        crate::leanh::lean_closure_set(v___f_3456_, 0, v_snd_3451_);
                        crate::leanh::lean_closure_set(v___f_3456_, 1, v_star_3435_);
                        crate::leanh::lean_closure_set(v___f_3456_, 2, v___x_3455_);
                        crate::leanh::lean_closure_set(v___f_3456_, 3, v_minorIdx_3437_);
                        crate::leanh::lean_closure_set(v___f_3456_, 4, v_recArgs_3439_);
                        crate::leanh::lean_closure_set(v___f_3456_, 5, v_motiveIds_3432_);
                        crate::leanh::lean_closure_set(v___f_3456_, 6, v_mainMotiveId_3433_);
                        crate::leanh::lean_closure_set(v___f_3456_, 7, v_unit_3434_);
                        crate::leanh::lean_closure_set(v___f_3456_, 8, v_minorEntries_3436_);
                        crate::leanh::lean_closure_set(v___f_3456_, 9, v_casesOnParams_3438_);
                        crate::leanh::lean_closure_set(v___f_3456_, 10, v_k_3440_);
                        crate::leanh::lean_closure_set(v___f_3456_, 11, v_a_3454_);
                        v___x_3457_ = l_Lean_LocalDecl_type(v_a_3454_);
                        crate::leanh::lean_dec(v_a_3454_);
                        v___x_3458_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___closed__0;
                        v___x_3459_ = (crate::leanh::lean_unbox(v_snd_3451_) as u8);
                        crate::leanh::lean_dec(v_snd_3451_);
                        v___x_3460_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_withMinorParams___redArg(v_motiveIds_3432_, v_mainMotiveId_3433_, v_unit_3434_, v___x_3457_, v___x_3459_, v___x_3458_, v___x_3458_, v___f_3456_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
                        return v___x_3460_;
                    } else {
                        crate::leanh::lean_dec(v_snd_3451_);
                        crate::leanh::lean_dec_ref(v_k_3440_);
                        crate::leanh::lean_dec_ref(v_recArgs_3439_);
                        crate::leanh::lean_dec_ref(v_casesOnParams_3438_);
                        crate::leanh::lean_dec(v_minorIdx_3437_);
                        crate::leanh::lean_dec_ref(v_minorEntries_3436_);
                        crate::leanh::lean_dec_ref(v_star_3435_);
                        crate::leanh::lean_dec_ref(v_unit_3434_);
                        crate::leanh::lean_dec(v_mainMotiveId_3433_);
                        crate::leanh::lean_dec_ref(v_motiveIds_3432_);
                        v_a_3461_ = crate::leanh::lean_ctor_get(v___x_3453_, 0);
                        v_isSharedCheck_3468_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3453_)) as u8;
                        if v_isSharedCheck_3468_ == 0 {
                            v___x_3463_ = v___x_3453_;
                            v_isShared_3464_ = v_isSharedCheck_3468_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3461_);
                            crate::leanh::lean_dec(v___x_3453_);
                            v___x_3463_ = crate::leanh::lean_box(0);
                            v_isShared_3464_ = v_isSharedCheck_3468_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3464_ == 0 {
                    v___x_3466_ = v___x_3463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
                    v___x_3466_ = v_reuseFailAlloc_3467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___lam__0(
    mut v_minorNonRecParams_3469_: *mut crate::leanh::LeanObject,
    mut v_minorParams_3470_: *mut crate::leanh::LeanObject,
    mut v___x_3471_: u8,
    mut v___x_3472_: u8,
    mut v___x_3473_: u8,
    mut v_minorIdx_3474_: *mut crate::leanh::LeanObject,
    mut v_casesOnParams_3475_: *mut crate::leanh::LeanObject,
    mut v_recArgs_3476_: *mut crate::leanh::LeanObject,
    mut v_motiveIds_3477_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3478_: *mut crate::leanh::LeanObject,
    mut v_unit_3479_: *mut crate::leanh::LeanObject,
    mut v_star_3480_: *mut crate::leanh::LeanObject,
    mut v_minorEntries_3481_: *mut crate::leanh::LeanObject,
    mut v_k_3482_: *mut crate::leanh::LeanObject,
    mut v_newC_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_newC_3483_);
                v___x_3489_ = l_Lean_mkAppN(v_newC_3483_, v_minorNonRecParams_3469_);
                v___x_3490_ = l_Lean_Meta_mkLambdaFVars(
                    v_minorParams_3470_,
                    v___x_3489_,
                    v___x_3471_,
                    v___x_3472_,
                    v___x_3471_,
                    v___x_3472_,
                    v___x_3473_,
                    v___y_3484_,
                    v___y_3485_,
                    v___y_3486_,
                    v___y_3487_,
                );
                if crate::leanh::lean_obj_tag(v___x_3490_) == 0 {
                    v_a_3491_ = crate::leanh::lean_ctor_get(v___x_3490_, 0);
                    crate::leanh::lean_inc(v_a_3491_);
                    crate::leanh::lean_dec_ref_known(v___x_3490_, 1);
                    v___x_3492_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3493_ = lean_nat_add(v_minorIdx_3474_, v___x_3492_);
                    v___x_3494_ = lean_array_push(v_casesOnParams_3475_, v_newC_3483_);
                    v___x_3495_ = lean_array_push(v_recArgs_3476_, v_a_3491_);
                    v___x_3496_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(v_motiveIds_3477_, v_mainMotiveId_3478_, v_unit_3479_, v_star_3480_, v_minorEntries_3481_, v___x_3493_, v___x_3494_, v___x_3495_, v_k_3482_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
                    return v___x_3496_;
                } else {
                    crate::leanh::lean_dec_ref(v_newC_3483_);
                    crate::leanh::lean_dec_ref(v_k_3482_);
                    crate::leanh::lean_dec_ref(v_minorEntries_3481_);
                    crate::leanh::lean_dec_ref(v_star_3480_);
                    crate::leanh::lean_dec_ref(v_unit_3479_);
                    crate::leanh::lean_dec(v_mainMotiveId_3478_);
                    crate::leanh::lean_dec_ref(v_motiveIds_3477_);
                    crate::leanh::lean_dec_ref(v_recArgs_3476_);
                    crate::leanh::lean_dec_ref(v_casesOnParams_3475_);
                    v_a_3497_ = crate::leanh::lean_ctor_get(v___x_3490_, 0);
                    v_isSharedCheck_3504_ = (!crate::leanh::lean_is_exclusive(v___x_3490_)) as u8;
                    if v_isSharedCheck_3504_ == 0 {
                        v___x_3499_ = v___x_3490_;
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3497_);
                        crate::leanh::lean_dec(v___x_3490_);
                        v___x_3499_ = crate::leanh::lean_box(0);
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3500_ == 0 {
                    v___x_3502_ = v___x_3499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
                    v___x_3502_ = v_reuseFailAlloc_3503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg___boxed(
    mut v_motiveIds_3505_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3506_: *mut crate::leanh::LeanObject,
    mut v_unit_3507_: *mut crate::leanh::LeanObject,
    mut v_star_3508_: *mut crate::leanh::LeanObject,
    mut v_minorEntries_3509_: *mut crate::leanh::LeanObject,
    mut v_minorIdx_3510_: *mut crate::leanh::LeanObject,
    mut v_casesOnParams_3511_: *mut crate::leanh::LeanObject,
    mut v_recArgs_3512_: *mut crate::leanh::LeanObject,
    mut v_k_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
    mut v_a_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3519_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(
        v_motiveIds_3505_,
        v_mainMotiveId_3506_,
        v_unit_3507_,
        v_star_3508_,
        v_minorEntries_3509_,
        v_minorIdx_3510_,
        v_casesOnParams_3511_,
        v_recArgs_3512_,
        v_k_3513_,
        v_a_3514_,
        v_a_3515_,
        v_a_3516_,
        v_a_3517_,
    );
    crate::leanh::lean_dec(v_a_3517_);
    crate::leanh::lean_dec_ref(v_a_3516_);
    crate::leanh::lean_dec(v_a_3515_);
    crate::leanh::lean_dec_ref(v_a_3514_);
    return v_res_3519_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors(
    mut v_00_u03b1_3520_: *mut crate::leanh::LeanObject,
    mut v_indNames_3521_: *mut crate::leanh::LeanObject,
    mut v_numParams_3522_: *mut crate::leanh::LeanObject,
    mut v_numMotives_3523_: *mut crate::leanh::LeanObject,
    mut v_numMinors_3524_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3525_: *mut crate::leanh::LeanObject,
    mut v_motiveIds_3526_: *mut crate::leanh::LeanObject,
    mut v_mainMotiveId_3527_: *mut crate::leanh::LeanObject,
    mut v_unit_3528_: *mut crate::leanh::LeanObject,
    mut v_star_3529_: *mut crate::leanh::LeanObject,
    mut v_minorEntries_3530_: *mut crate::leanh::LeanObject,
    mut v_minorIdx_3531_: *mut crate::leanh::LeanObject,
    mut v_casesOnParams_3532_: *mut crate::leanh::LeanObject,
    mut v_recArgs_3533_: *mut crate::leanh::LeanObject,
    mut v_k_3534_: *mut crate::leanh::LeanObject,
    mut v_a_3535_: *mut crate::leanh::LeanObject,
    mut v_a_3536_: *mut crate::leanh::LeanObject,
    mut v_a_3537_: *mut crate::leanh::LeanObject,
    mut v_a_3538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3540_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(
        v_motiveIds_3526_,
        v_mainMotiveId_3527_,
        v_unit_3528_,
        v_star_3529_,
        v_minorEntries_3530_,
        v_minorIdx_3531_,
        v_casesOnParams_3532_,
        v_recArgs_3533_,
        v_k_3534_,
        v_a_3535_,
        v_a_3536_,
        v_a_3537_,
        v_a_3538_,
    );
    return v___x_3540_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03b1_3541_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_indNames_3542_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_numParams_3543_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_numMotives_3544_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_numMinors_3545_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_recFVars_3546_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_motiveIds_3547_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_mainMotiveId_3548_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_unit_3549_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_star_3550_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_minorEntries_3551_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_minorIdx_3552_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_casesOnParams_3553_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_recArgs_3554_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_k_3555_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3556_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3557_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_3558_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_3559_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_3560_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3561_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors(
        v_00_u03b1_3541_,
        v_indNames_3542_,
        v_numParams_3543_,
        v_numMotives_3544_,
        v_numMinors_3545_,
        v_recFVars_3546_,
        v_motiveIds_3547_,
        v_mainMotiveId_3548_,
        v_unit_3549_,
        v_star_3550_,
        v_minorEntries_3551_,
        v_minorIdx_3552_,
        v_casesOnParams_3553_,
        v_recArgs_3554_,
        v_k_3555_,
        v_a_3556_,
        v_a_3557_,
        v_a_3558_,
        v_a_3559_,
    );
    crate::leanh::lean_dec(v_a_3559_);
    crate::leanh::lean_dec_ref(v_a_3558_);
    crate::leanh::lean_dec(v_a_3557_);
    crate::leanh::lean_dec_ref(v_a_3556_);
    crate::leanh::lean_dec_ref(v_recFVars_3546_);
    crate::leanh::lean_dec(v_numMinors_3545_);
    crate::leanh::lean_dec(v_numMotives_3544_);
    crate::leanh::lean_dec(v_numParams_3543_);
    crate::leanh::lean_dec_ref(v_indNames_3542_);
    return v_res_3561_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg(
    mut v_name_3562_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3563_: *mut crate::leanh::LeanObject,
    mut v_type_3564_: *mut crate::leanh::LeanObject,
    mut v_value_3565_: *mut crate::leanh::LeanObject,
    mut v_hints_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: u8 = 0;
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: u8 = 0;
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: u8 = 0;
    let mut v_env_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3569_ = lean_st_ref_get(v___y_3567_);
                v_env_3581_ = crate::leanh::lean_ctor_get(v___x_3569_, 0);
                crate::leanh::lean_inc_ref_n(v_env_3581_, 2);
                crate::leanh::lean_dec(v___x_3569_);
                v___x_3582_ = l_Lean_Environment_hasUnsafe(v_env_3581_, v_type_3564_);
                if v___x_3582_ == 0 {
                    v___x_3583_ = l_Lean_Environment_hasUnsafe(v_env_3581_, v_value_3565_);
                    v___y_3578_ = v___x_3583_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_3581_);
                    v___y_3578_ = v___x_3582_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_name_3562_);
                v___x_3572_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3572_, 0, v_name_3562_);
                crate::leanh::lean_ctor_set(v___x_3572_, 1, v_levelParams_3563_);
                crate::leanh::lean_ctor_set(v___x_3572_, 2, v_type_3564_);
                v___x_3573_ = crate::leanh::lean_box(0);
                v___x_3574_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3574_, 0, v_name_3562_);
                crate::leanh::lean_ctor_set(v___x_3574_, 1, v___x_3573_);
                v___x_3575_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3575_, 0, v___x_3572_);
                crate::leanh::lean_ctor_set(v___x_3575_, 1, v_value_3565_);
                crate::leanh::lean_ctor_set(v___x_3575_, 2, v_hints_3566_);
                crate::leanh::lean_ctor_set(v___x_3575_, 3, v___x_3574_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3575_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_3571_,
                );
                v___x_3576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3576_, 0, v___x_3575_);
                return v___x_3576_;
            }
            2 => {
                if v___y_3578_ == 0 {
                    v___x_3579_ = 1;
                    v___y_3571_ = v___x_3579_;
                    state = 1;
                    continue;
                } else {
                    v___x_3580_ = 0;
                    v___y_3571_ = v___x_3580_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg___boxed(
    mut v_name_3584_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3585_: *mut crate::leanh::LeanObject,
    mut v_type_3586_: *mut crate::leanh::LeanObject,
    mut v_value_3587_: *mut crate::leanh::LeanObject,
    mut v_hints_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg(v_name_3584_, v_levelParams_3585_, v_type_3586_, v_value_3587_, v_hints_3588_, v___y_3589_);
    crate::leanh::lean_dec(v___y_3589_);
    return v_res_3591_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8(
    mut v_name_3592_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3593_: *mut crate::leanh::LeanObject,
    mut v_type_3594_: *mut crate::leanh::LeanObject,
    mut v_value_3595_: *mut crate::leanh::LeanObject,
    mut v_hints_3596_: *mut crate::leanh::LeanObject,
    mut v___y_3597_: *mut crate::leanh::LeanObject,
    mut v___y_3598_: *mut crate::leanh::LeanObject,
    mut v___y_3599_: *mut crate::leanh::LeanObject,
    mut v___y_3600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3602_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg(v_name_3592_, v_levelParams_3593_, v_type_3594_, v_value_3595_, v_hints_3596_, v___y_3600_);
    return v___x_3602_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___boxed(
    mut v_name_3603_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3604_: *mut crate::leanh::LeanObject,
    mut v_type_3605_: *mut crate::leanh::LeanObject,
    mut v_value_3606_: *mut crate::leanh::LeanObject,
    mut v_hints_3607_: *mut crate::leanh::LeanObject,
    mut v___y_3608_: *mut crate::leanh::LeanObject,
    mut v___y_3609_: *mut crate::leanh::LeanObject,
    mut v___y_3610_: *mut crate::leanh::LeanObject,
    mut v___y_3611_: *mut crate::leanh::LeanObject,
    mut v___y_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8(v_name_3603_, v_levelParams_3604_, v_type_3605_, v_value_3606_, v_hints_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
    crate::leanh::lean_dec(v___y_3611_);
    crate::leanh::lean_dec_ref(v___y_3610_);
    crate::leanh::lean_dec(v___y_3609_);
    crate::leanh::lean_dec_ref(v___y_3608_);
    return v_res_3613_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___lam__0(
    mut v_k_3614_: *mut crate::leanh::LeanObject,
    mut v_b_3615_: *mut crate::leanh::LeanObject,
    mut v_c_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
    mut v___y_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3620_);
    crate::leanh::lean_inc_ref(v___y_3619_);
    crate::leanh::lean_inc(v___y_3618_);
    crate::leanh::lean_inc_ref(v___y_3617_);
    v___x_3622_ = crate::leanh::lean_apply_7(
        v_k_3614_,
        v_b_3615_,
        v_c_3616_,
        v___y_3617_,
        v___y_3618_,
        v___y_3619_,
        v___y_3620_,
        crate::leanh::lean_box(0),
    );
    return v___x_3622_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___lam__0___boxed(
    mut v_k_3623_: *mut crate::leanh::LeanObject,
    mut v_b_3624_: *mut crate::leanh::LeanObject,
    mut v_c_3625_: *mut crate::leanh::LeanObject,
    mut v___y_3626_: *mut crate::leanh::LeanObject,
    mut v___y_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3631_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___lam__0(v_k_3623_, v_b_3624_, v_c_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
    crate::leanh::lean_dec(v___y_3629_);
    crate::leanh::lean_dec_ref(v___y_3628_);
    crate::leanh::lean_dec(v___y_3627_);
    crate::leanh::lean_dec_ref(v___y_3626_);
    return v_res_3631_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg(
    mut v_type_3632_: *mut crate::leanh::LeanObject,
    mut v_k_3633_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3634_: u8,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
    mut v___y_3637_: *mut crate::leanh::LeanObject,
    mut v___y_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v_a_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3655_: u8 = 0;
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3640_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_3640_, 0, v_k_3633_);
                v___x_3641_ = 0;
                v___x_3642_ = crate::leanh::lean_box(0);
                v___x_3643_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_3641_,
                        v___x_3642_,
                        v_type_3632_,
                        v___f_3640_,
                        v_cleanupAnnotations_3634_,
                        v___x_3641_,
                        v___y_3635_,
                        v___y_3636_,
                        v___y_3637_,
                        v___y_3638_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3643_) == 0 {
                    v_a_3644_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                    v_isSharedCheck_3651_ = (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3651_ == 0 {
                        v___x_3646_ = v___x_3643_;
                        v_isShared_3647_ = v_isSharedCheck_3651_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3644_);
                        crate::leanh::lean_dec(v___x_3643_);
                        v___x_3646_ = crate::leanh::lean_box(0);
                        v_isShared_3647_ = v_isSharedCheck_3651_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3652_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                    v_isSharedCheck_3659_ = (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                    if v_isSharedCheck_3659_ == 0 {
                        v___x_3654_ = v___x_3643_;
                        v_isShared_3655_ = v_isSharedCheck_3659_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3652_);
                        crate::leanh::lean_dec(v___x_3643_);
                        v___x_3654_ = crate::leanh::lean_box(0);
                        v_isShared_3655_ = v_isSharedCheck_3659_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3647_ == 0 {
                    v___x_3649_ = v___x_3646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
                    v___x_3649_ = v_reuseFailAlloc_3650_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3649_;
            }
            3 => {
                if v_isShared_3655_ == 0 {
                    v___x_3657_ = v___x_3654_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
                    v___x_3657_ = v_reuseFailAlloc_3658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg___boxed(
    mut v_type_3660_: *mut crate::leanh::LeanObject,
    mut v_k_3661_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3662_: *mut crate::leanh::LeanObject,
    mut v___y_3663_: *mut crate::leanh::LeanObject,
    mut v___y_3664_: *mut crate::leanh::LeanObject,
    mut v___y_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3668_: u8 = 0;
    let mut v_res_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3668_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3662_) as u8);
    v_res_3669_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg(v_type_3660_, v_k_3661_, v_cleanupAnnotations_boxed_3668_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
    crate::leanh::lean_dec(v___y_3666_);
    crate::leanh::lean_dec_ref(v___y_3665_);
    crate::leanh::lean_dec(v___y_3664_);
    crate::leanh::lean_dec_ref(v___y_3663_);
    return v_res_3669_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12(
    mut v_00_u03b1_3670_: *mut crate::leanh::LeanObject,
    mut v_type_3671_: *mut crate::leanh::LeanObject,
    mut v_k_3672_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3673_: u8,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
    mut v___y_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3679_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg(v_type_3671_, v_k_3672_, v_cleanupAnnotations_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
    return v___x_3679_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___boxed(
    mut v_00_u03b1_3680_: *mut crate::leanh::LeanObject,
    mut v_type_3681_: *mut crate::leanh::LeanObject,
    mut v_k_3682_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3689_: u8 = 0;
    let mut v_res_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3689_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3683_) as u8);
    v_res_3690_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12(v_00_u03b1_3680_, v_type_3681_, v_k_3682_, v_cleanupAnnotations_boxed_3689_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
    crate::leanh::lean_dec(v___y_3687_);
    crate::leanh::lean_dec_ref(v___y_3686_);
    crate::leanh::lean_dec(v___y_3685_);
    crate::leanh::lean_dec_ref(v___y_3684_);
    return v_res_3690_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(
    mut v___x_3691_: *mut crate::leanh::LeanObject,
    mut v___x_3692_: *mut crate::leanh::LeanObject,
    mut v___x_3693_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3694_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3695_: *mut crate::leanh::LeanObject,
    mut v_b_3696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3695_) == 0 {
                    v___x_3698_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3698_, 0, v_b_3696_);
                    return v___x_3698_;
                } else {
                    v_head_3699_ = crate::leanh::lean_ctor_get(v_as_x27_3695_, 0);
                    v_tail_3700_ = crate::leanh::lean_ctor_get(v_as_x27_3695_, 1);
                    v___x_3701_ = l_Lean_instInhabitedExpr;
                    v___x_3702_ = lean_nat_add(v___x_3691_, v___x_3692_);
                    v___x_3703_ = lean_nat_add(v___x_3702_, v___x_3693_);
                    crate::leanh::lean_dec(v___x_3702_);
                    v___x_3704_ = lean_nat_add(v___x_3703_, v_head_3699_);
                    crate::leanh::lean_dec(v___x_3703_);
                    v___x_3705_ =
                        lean_array_get_borrowed(v___x_3701_, v_recFVars_3694_, v___x_3704_);
                    crate::leanh::lean_dec(v___x_3704_);
                    crate::leanh::lean_inc(v___x_3705_);
                    v___x_3706_ = lean_array_push(v_b_3696_, v___x_3705_);
                    v_as_x27_3695_ = v_tail_3700_;
                    v_b_3696_ = v___x_3706_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg___boxed(
    mut v___x_3708_: *mut crate::leanh::LeanObject,
    mut v___x_3709_: *mut crate::leanh::LeanObject,
    mut v___x_3710_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3711_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3712_: *mut crate::leanh::LeanObject,
    mut v_b_3713_: *mut crate::leanh::LeanObject,
    mut v___y_3714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3715_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(v___x_3708_, v___x_3709_, v___x_3710_, v_recFVars_3711_, v_as_x27_3712_, v_b_3713_);
    crate::leanh::lean_dec(v_as_x27_3712_);
    crate::leanh::lean_dec_ref(v_recFVars_3711_);
    crate::leanh::lean_dec(v___x_3710_);
    crate::leanh::lean_dec(v___x_3709_);
    crate::leanh::lean_dec(v___x_3708_);
    return v_res_3715_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__0(
    mut v_numParams_3716_: *mut crate::leanh::LeanObject,
    mut v_numMotives_3717_: *mut crate::leanh::LeanObject,
    mut v_numMinors_3718_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3719_: *mut crate::leanh::LeanObject,
    mut v___x_3720_: *mut crate::leanh::LeanObject,
    mut v_recType_3721_: *mut crate::leanh::LeanObject,
    mut v___x_3722_: u8,
    mut v___x_3723_: *mut crate::leanh::LeanObject,
    mut v___x_3724_: *mut crate::leanh::LeanObject,
    mut v___x_3725_: *mut crate::leanh::LeanObject,
    mut v_casesOnParams_3726_: *mut crate::leanh::LeanObject,
    mut v_recArgs_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3750_: u8 = 0;
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3757_: u8 = 0;
    let mut v_a_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3765_: u8 = 0;
    let mut v_a_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3773_: u8 = 0;
    let mut v_isSharedCheck_3774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3733_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(v_numParams_3716_, v_numMotives_3717_, v_numMinors_3718_, v_recFVars_3719_, v___x_3720_, v_recArgs_3727_);
                v_a_3734_ = crate::leanh::lean_ctor_get(v___x_3733_, 0);
                v_isSharedCheck_3774_ = (!crate::leanh::lean_is_exclusive(v___x_3733_)) as u8;
                if v_isSharedCheck_3774_ == 0 {
                    v___x_3736_ = v___x_3733_;
                    v_isShared_3737_ = v_isSharedCheck_3774_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3734_);
                    crate::leanh::lean_dec(v___x_3733_);
                    v___x_3736_ = crate::leanh::lean_box(0);
                    v_isShared_3737_ = v_isSharedCheck_3774_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3738_ = 0;
                v___x_3739_ = 1;
                v___x_3740_ = l_Lean_Meta_mkForallFVars(
                    v_casesOnParams_3726_,
                    v_recType_3721_,
                    v___x_3738_,
                    v___x_3722_,
                    v___x_3722_,
                    v___x_3739_,
                    v___y_3728_,
                    v___y_3729_,
                    v___y_3730_,
                    v___y_3731_,
                );
                if crate::leanh::lean_obj_tag(v___x_3740_) == 0 {
                    v_a_3741_ = crate::leanh::lean_ctor_get(v___x_3740_, 0);
                    crate::leanh::lean_inc(v_a_3741_);
                    crate::leanh::lean_dec_ref_known(v___x_3740_, 1);
                    v___x_3742_ = l_Lean_mkAppN(v___x_3723_, v_a_3734_);
                    crate::leanh::lean_dec(v_a_3734_);
                    v___x_3743_ = l_Lean_Meta_mkLambdaFVars(
                        v_casesOnParams_3726_,
                        v___x_3742_,
                        v___x_3738_,
                        v___x_3722_,
                        v___x_3738_,
                        v___x_3722_,
                        v___x_3739_,
                        v___y_3728_,
                        v___y_3729_,
                        v___y_3730_,
                        v___y_3731_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3743_) == 0 {
                        v_a_3744_ = crate::leanh::lean_ctor_get(v___x_3743_, 0);
                        crate::leanh::lean_inc(v_a_3744_);
                        crate::leanh::lean_dec_ref_known(v___x_3743_, 1);
                        v___x_3745_ = crate::leanh::lean_box(1);
                        v___x_3746_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__8___redArg(v___x_3724_, v___x_3725_, v_a_3741_, v_a_3744_, v___x_3745_, v___y_3731_);
                        v_a_3747_ = crate::leanh::lean_ctor_get(v___x_3746_, 0);
                        v_isSharedCheck_3757_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3746_)) as u8;
                        if v_isSharedCheck_3757_ == 0 {
                            v___x_3749_ = v___x_3746_;
                            v_isShared_3750_ = v_isSharedCheck_3757_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3747_);
                            crate::leanh::lean_dec(v___x_3746_);
                            v___x_3749_ = crate::leanh::lean_box(0);
                            v_isShared_3750_ = v_isSharedCheck_3757_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3741_);
                        crate::leanh::lean_del_object(v___x_3736_);
                        crate::leanh::lean_dec(v___x_3725_);
                        crate::leanh::lean_dec(v___x_3724_);
                        v_a_3758_ = crate::leanh::lean_ctor_get(v___x_3743_, 0);
                        v_isSharedCheck_3765_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3743_)) as u8;
                        if v_isSharedCheck_3765_ == 0 {
                            v___x_3760_ = v___x_3743_;
                            v_isShared_3761_ = v_isSharedCheck_3765_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3758_);
                            crate::leanh::lean_dec(v___x_3743_);
                            v___x_3760_ = crate::leanh::lean_box(0);
                            v_isShared_3761_ = v_isSharedCheck_3765_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3736_);
                    crate::leanh::lean_dec(v_a_3734_);
                    crate::leanh::lean_dec(v___x_3725_);
                    crate::leanh::lean_dec(v___x_3724_);
                    crate::leanh::lean_dec_ref(v___x_3723_);
                    v_a_3766_ = crate::leanh::lean_ctor_get(v___x_3740_, 0);
                    v_isSharedCheck_3773_ = (!crate::leanh::lean_is_exclusive(v___x_3740_)) as u8;
                    if v_isSharedCheck_3773_ == 0 {
                        v___x_3768_ = v___x_3740_;
                        v_isShared_3769_ = v_isSharedCheck_3773_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3766_);
                        crate::leanh::lean_dec(v___x_3740_);
                        v___x_3768_ = crate::leanh::lean_box(0);
                        v_isShared_3769_ = v_isSharedCheck_3773_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3737_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3736_, 1);
                    crate::leanh::lean_ctor_set(v___x_3736_, 0, v_a_3747_);
                    v___x_3752_ = v___x_3736_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3747_);
                    v___x_3752_ = v_reuseFailAlloc_3756_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3750_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3749_, 0, v___x_3752_);
                    v___x_3754_ = v___x_3749_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3752_);
                    v___x_3754_ = v_reuseFailAlloc_3755_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3754_;
            }
            5 => {
                if v_isShared_3761_ == 0 {
                    v___x_3763_ = v___x_3760_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
                    v___x_3763_ = v_reuseFailAlloc_3764_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3763_;
            }
            7 => {
                if v_isShared_3769_ == 0 {
                    v___x_3771_ = v___x_3768_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
                    v___x_3771_ = v_reuseFailAlloc_3772_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numParams_3775_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_numMotives_3776_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_numMinors_3777_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_recFVars_3778_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3779_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_recType_3780_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3781_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3782_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_3783_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_3784_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_casesOnParams_3785_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_recArgs_3786_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3787_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3788_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3789_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3790_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3791_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_12918__boxed_3792_: u8 = 0;
    let mut v_res_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12918__boxed_3792_ = (crate::leanh::lean_unbox(v___x_3781_) as u8);
    v_res_3793_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__0(
        v_numParams_3775_,
        v_numMotives_3776_,
        v_numMinors_3777_,
        v_recFVars_3778_,
        v___x_3779_,
        v_recType_3780_,
        v___x_12918__boxed_3792_,
        v___x_3782_,
        v___x_3783_,
        v___x_3784_,
        v_casesOnParams_3785_,
        v_recArgs_3786_,
        v___y_3787_,
        v___y_3788_,
        v___y_3789_,
        v___y_3790_,
    );
    crate::leanh::lean_dec(v___y_3790_);
    crate::leanh::lean_dec_ref(v___y_3789_);
    crate::leanh::lean_dec(v___y_3788_);
    crate::leanh::lean_dec_ref(v___y_3787_);
    crate::leanh::lean_dec_ref(v_casesOnParams_3785_);
    crate::leanh::lean_dec(v___x_3779_);
    crate::leanh::lean_dec_ref(v_recFVars_3778_);
    crate::leanh::lean_dec(v_numMinors_3777_);
    crate::leanh::lean_dec(v_numMotives_3776_);
    crate::leanh::lean_dec(v_numParams_3775_);
    return v_res_3793_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg(
    mut v___x_3794_: *mut crate::leanh::LeanObject,
    mut v___x_3795_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3796_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3797_: *mut crate::leanh::LeanObject,
    mut v_b_3798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3797_) == 0 {
                    v___x_3800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3800_, 0, v_b_3798_);
                    return v___x_3800_;
                } else {
                    v_tail_3801_ = crate::leanh::lean_ctor_get(v_as_x27_3797_, 1);
                    v_fst_3802_ = crate::leanh::lean_ctor_get(v_b_3798_, 0);
                    v_snd_3803_ = crate::leanh::lean_ctor_get(v_b_3798_, 1);
                    v_isSharedCheck_3821_ = (!crate::leanh::lean_is_exclusive(v_b_3798_)) as u8;
                    if v_isSharedCheck_3821_ == 0 {
                        v___x_3805_ = v_b_3798_;
                        v_isShared_3806_ = v_isSharedCheck_3821_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3803_);
                        crate::leanh::lean_inc(v_fst_3802_);
                        crate::leanh::lean_dec(v_b_3798_);
                        v___x_3805_ = crate::leanh::lean_box(0);
                        v_isShared_3806_ = v_isSharedCheck_3821_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3807_ = l_Lean_instInhabitedExpr;
                v___x_3808_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3809_ = lean_nat_add(v___x_3794_, v___x_3795_);
                v___x_3810_ = lean_nat_add(v___x_3809_, v_snd_3803_);
                crate::leanh::lean_dec(v___x_3809_);
                v___x_3811_ = lean_array_get_borrowed(v___x_3807_, v_recFVars_3796_, v___x_3810_);
                crate::leanh::lean_dec(v___x_3810_);
                v___x_3812_ = 0;
                v___x_3813_ = crate::leanh::lean_box((v___x_3812_) as usize);
                crate::leanh::lean_inc(v___x_3811_);
                if v_isShared_3806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3805_, 1, v___x_3813_);
                    crate::leanh::lean_ctor_set(v___x_3805_, 0, v___x_3811_);
                    v___x_3815_ = v___x_3805_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___x_3813_);
                    v___x_3815_ = v_reuseFailAlloc_3820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3816_ = lean_array_push(v_fst_3802_, v___x_3815_);
                v___x_3817_ = lean_nat_add(v_snd_3803_, v___x_3808_);
                crate::leanh::lean_dec(v_snd_3803_);
                v___x_3818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3818_, 0, v___x_3816_);
                crate::leanh::lean_ctor_set(v___x_3818_, 1, v___x_3817_);
                v_as_x27_3797_ = v_tail_3801_;
                v_b_3798_ = v___x_3818_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg___boxed(
    mut v___x_3822_: *mut crate::leanh::LeanObject,
    mut v___x_3823_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3824_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3825_: *mut crate::leanh::LeanObject,
    mut v_b_3826_: *mut crate::leanh::LeanObject,
    mut v___y_3827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3828_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg(v___x_3822_, v___x_3823_, v_recFVars_3824_, v_as_x27_3825_, v_b_3826_);
    crate::leanh::lean_dec(v_as_x27_3825_);
    crate::leanh::lean_dec_ref(v_recFVars_3824_);
    crate::leanh::lean_dec(v___x_3823_);
    crate::leanh::lean_dec(v___x_3822_);
    return v_res_3828_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg(
    mut v___x_3829_: *mut crate::leanh::LeanObject,
    mut v___x_3830_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3831_: *mut crate::leanh::LeanObject,
    mut v_a_3832_: *mut crate::leanh::LeanObject,
    mut v_declName_3833_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3834_: *mut crate::leanh::LeanObject,
    mut v_b_3835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: u8 = 0;
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3834_) == 0 {
                    v___x_3837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3837_, 0, v_b_3835_);
                    return v___x_3837_;
                } else {
                    v_tail_3838_ = crate::leanh::lean_ctor_get(v_as_x27_3834_, 1);
                    v_fst_3839_ = crate::leanh::lean_ctor_get(v_b_3835_, 0);
                    v_snd_3840_ = crate::leanh::lean_ctor_get(v_b_3835_, 1);
                    v_isSharedCheck_3858_ = (!crate::leanh::lean_is_exclusive(v_b_3835_)) as u8;
                    if v_isSharedCheck_3858_ == 0 {
                        v___x_3842_ = v_b_3835_;
                        v_isShared_3843_ = v_isSharedCheck_3858_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3840_);
                        crate::leanh::lean_inc(v_fst_3839_);
                        crate::leanh::lean_dec(v_b_3835_);
                        v___x_3842_ = crate::leanh::lean_box(0);
                        v_isShared_3843_ = v_isSharedCheck_3858_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3844_ = l_Lean_instInhabitedExpr;
                v___x_3845_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3846_ = lean_nat_add(v___x_3829_, v___x_3830_);
                v___x_3847_ = lean_nat_add(v___x_3846_, v_snd_3840_);
                crate::leanh::lean_dec(v___x_3846_);
                v___x_3848_ = lean_array_get_borrowed(v___x_3844_, v_recFVars_3831_, v___x_3847_);
                crate::leanh::lean_dec(v___x_3847_);
                v___x_3849_ = lean_name_eq(v_a_3832_, v_declName_3833_);
                v___x_3850_ = crate::leanh::lean_box((v___x_3849_) as usize);
                crate::leanh::lean_inc(v___x_3848_);
                if v_isShared_3843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3842_, 1, v___x_3850_);
                    crate::leanh::lean_ctor_set(v___x_3842_, 0, v___x_3848_);
                    v___x_3852_ = v___x_3842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 1, v___x_3850_);
                    v___x_3852_ = v_reuseFailAlloc_3857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3853_ = lean_array_push(v_fst_3839_, v___x_3852_);
                v___x_3854_ = lean_nat_add(v_snd_3840_, v___x_3845_);
                crate::leanh::lean_dec(v_snd_3840_);
                v___x_3855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3855_, 0, v___x_3853_);
                crate::leanh::lean_ctor_set(v___x_3855_, 1, v___x_3854_);
                v_as_x27_3834_ = v_tail_3838_;
                v_b_3835_ = v___x_3855_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg___boxed(
    mut v___x_3859_: *mut crate::leanh::LeanObject,
    mut v___x_3860_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3861_: *mut crate::leanh::LeanObject,
    mut v_a_3862_: *mut crate::leanh::LeanObject,
    mut v_declName_3863_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3864_: *mut crate::leanh::LeanObject,
    mut v_b_3865_: *mut crate::leanh::LeanObject,
    mut v___y_3866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3867_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg(v___x_3859_, v___x_3860_, v_recFVars_3861_, v_a_3862_, v_declName_3863_, v_as_x27_3864_, v_b_3865_);
    crate::leanh::lean_dec(v_as_x27_3864_);
    crate::leanh::lean_dec(v_declName_3863_);
    crate::leanh::lean_dec(v_a_3862_);
    crate::leanh::lean_dec_ref(v_recFVars_3861_);
    crate::leanh::lean_dec(v___x_3860_);
    crate::leanh::lean_dec(v___x_3859_);
    return v_res_3867_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13(
    mut v_msgData_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
    mut v___y_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = lean_st_ref_get(v___y_3872_);
    v_env_3875_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
    crate::leanh::lean_inc_ref(v_env_3875_);
    crate::leanh::lean_dec(v___x_3874_);
    v___x_3876_ = lean_st_ref_get(v___y_3870_);
    v_mctx_3877_ = crate::leanh::lean_ctor_get(v___x_3876_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3877_);
    crate::leanh::lean_dec(v___x_3876_);
    v_lctx_3878_ = crate::leanh::lean_ctor_get(v___y_3869_, 2);
    v_options_3879_ = crate::leanh::lean_ctor_get(v___y_3871_, 2);
    crate::leanh::lean_inc_ref(v_options_3879_);
    crate::leanh::lean_inc_ref(v_lctx_3878_);
    v___x_3880_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3880_, 0, v_env_3875_);
    crate::leanh::lean_ctor_set(v___x_3880_, 1, v_mctx_3877_);
    crate::leanh::lean_ctor_set(v___x_3880_, 2, v_lctx_3878_);
    crate::leanh::lean_ctor_set(v___x_3880_, 3, v_options_3879_);
    v___x_3881_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3881_, 0, v___x_3880_);
    crate::leanh::lean_ctor_set(v___x_3881_, 1, v_msgData_3868_);
    v___x_3882_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3882_, 0, v___x_3881_);
    return v___x_3882_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13___boxed(
    mut v_msgData_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
    mut v___y_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
    mut v___y_3888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3889_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13(v_msgData_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
    crate::leanh::lean_dec(v___y_3887_);
    crate::leanh::lean_dec_ref(v___y_3886_);
    crate::leanh::lean_dec(v___y_3885_);
    crate::leanh::lean_dec_ref(v___y_3884_);
    return v_res_3889_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(
    mut v_msg_3890_: *mut crate::leanh::LeanObject,
    mut v___y_3891_: *mut crate::leanh::LeanObject,
    mut v___y_3892_: *mut crate::leanh::LeanObject,
    mut v___y_3893_: *mut crate::leanh::LeanObject,
    mut v___y_3894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3896_ = crate::leanh::lean_ctor_get(v___y_3893_, 5);
                v___x_3897_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13(v_msg_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
                v_a_3898_ = crate::leanh::lean_ctor_get(v___x_3897_, 0);
                v_isSharedCheck_3906_ = (!crate::leanh::lean_is_exclusive(v___x_3897_)) as u8;
                if v_isSharedCheck_3906_ == 0 {
                    v___x_3900_ = v___x_3897_;
                    v_isShared_3901_ = v_isSharedCheck_3906_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3898_);
                    crate::leanh::lean_dec(v___x_3897_);
                    v___x_3900_ = crate::leanh::lean_box(0);
                    v_isShared_3901_ = v_isSharedCheck_3906_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3896_);
                v___x_3902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3902_, 0, v_ref_3896_);
                crate::leanh::lean_ctor_set(v___x_3902_, 1, v_a_3898_);
                if v_isShared_3901_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3900_, 1);
                    crate::leanh::lean_ctor_set(v___x_3900_, 0, v___x_3902_);
                    v___x_3904_ = v___x_3900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
                    v___x_3904_ = v_reuseFailAlloc_3905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg___boxed(
    mut v_msg_3907_: *mut crate::leanh::LeanObject,
    mut v___y_3908_: *mut crate::leanh::LeanObject,
    mut v___y_3909_: *mut crate::leanh::LeanObject,
    mut v___y_3910_: *mut crate::leanh::LeanObject,
    mut v___y_3911_: *mut crate::leanh::LeanObject,
    mut v___y_3912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v_msg_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
    crate::leanh::lean_dec(v___y_3911_);
    crate::leanh::lean_dec_ref(v___y_3910_);
    crate::leanh::lean_dec(v___y_3909_);
    crate::leanh::lean_dec_ref(v___y_3908_);
    return v_res_3913_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3915_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__0;
    v___x_3916_ = l_Lean_stringToMessageData(v___x_3915_);
    return v___x_3916_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3918_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__2;
    v___x_3919_ = l_Lean_stringToMessageData(v___x_3918_);
    return v___x_3919_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0(
    mut v_constName_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
    mut v___y_3923_: *mut crate::leanh::LeanObject,
    mut v___y_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u8 = 0;
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3926_ = lean_st_ref_get(v___y_3924_);
                v_env_3927_ = crate::leanh::lean_ctor_get(v___x_3926_, 0);
                crate::leanh::lean_inc_ref(v_env_3927_);
                crate::leanh::lean_dec(v___x_3926_);
                crate::leanh::lean_inc(v_constName_3920_);
                v___x_3928_ = l_Lean_isInductiveCore_x3f(v_env_3927_, v_constName_3920_);
                if crate::leanh::lean_obj_tag(v___x_3928_) == 0 {
                    v___x_3929_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1);
                    v___x_3930_ = 0;
                    v___x_3931_ = l_Lean_MessageData_ofConstName(v_constName_3920_, v___x_3930_);
                    v___x_3932_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3932_, 0, v___x_3929_);
                    crate::leanh::lean_ctor_set(v___x_3932_, 1, v___x_3931_);
                    v___x_3933_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__3);
                    v___x_3934_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3934_, 0, v___x_3932_);
                    crate::leanh::lean_ctor_set(v___x_3934_, 1, v___x_3933_);
                    v___x_3935_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v___x_3934_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
                    return v___x_3935_;
                } else {
                    crate::leanh::lean_dec(v_constName_3920_);
                    v_val_3936_ = crate::leanh::lean_ctor_get(v___x_3928_, 0);
                    v_isSharedCheck_3943_ = (!crate::leanh::lean_is_exclusive(v___x_3928_)) as u8;
                    if v_isSharedCheck_3943_ == 0 {
                        v___x_3938_ = v___x_3928_;
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3936_);
                        crate::leanh::lean_dec(v___x_3928_);
                        v___x_3938_ = crate::leanh::lean_box(0);
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3939_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3938_, 0);
                    v___x_3941_ = v___x_3938_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_val_3936_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___boxed(
    mut v_constName_3944_: *mut crate::leanh::LeanObject,
    mut v___y_3945_: *mut crate::leanh::LeanObject,
    mut v___y_3946_: *mut crate::leanh::LeanObject,
    mut v___y_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3950_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0(v_constName_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
    crate::leanh::lean_dec(v___y_3948_);
    crate::leanh::lean_dec_ref(v___y_3947_);
    crate::leanh::lean_dec(v___y_3946_);
    crate::leanh::lean_dec_ref(v___y_3945_);
    return v_res_3950_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__9(
    mut v___x_3951_: *mut crate::leanh::LeanObject,
    mut v___x_3952_: *mut crate::leanh::LeanObject,
    mut v_recFVars_3953_: *mut crate::leanh::LeanObject,
    mut v_declName_3954_: *mut crate::leanh::LeanObject,
    mut v_as_3955_: *mut crate::leanh::LeanObject,
    mut v_sz_3956_: usize,
    mut v_i_3957_: usize,
    mut v_b_3958_: *mut crate::leanh::LeanObject,
    mut v___y_3959_: *mut crate::leanh::LeanObject,
    mut v___y_3960_: *mut crate::leanh::LeanObject,
    mut v___y_3961_: *mut crate::leanh::LeanObject,
    mut v___y_3962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3973_: u8 = 0;
    let mut v_ctors_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: usize = 0;
    let mut v___x_3987_: usize = 0;
    let mut v_reuseFailAlloc_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut v_reuseFailAlloc_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3992_: u8 = 0;
    let mut v_a_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3996_: u8 = 0;
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3964_ = lean_usize_dec_lt(v_i_3957_, v_sz_3956_);
                if v___x_3964_ == 0 {
                    v___x_3965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3965_, 0, v_b_3958_);
                    return v___x_3965_;
                } else {
                    v_a_3966_ = lean_array_uget_borrowed(v_as_3955_, v_i_3957_);
                    crate::leanh::lean_inc(v_a_3966_);
                    v___x_3967_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0(v_a_3966_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
                    if crate::leanh::lean_obj_tag(v___x_3967_) == 0 {
                        v_a_3968_ = crate::leanh::lean_ctor_get(v___x_3967_, 0);
                        crate::leanh::lean_inc(v_a_3968_);
                        crate::leanh::lean_dec_ref_known(v___x_3967_, 1);
                        v_fst_3969_ = crate::leanh::lean_ctor_get(v_b_3958_, 0);
                        v_snd_3970_ = crate::leanh::lean_ctor_get(v_b_3958_, 1);
                        v_isSharedCheck_3992_ = (!crate::leanh::lean_is_exclusive(v_b_3958_)) as u8;
                        if v_isSharedCheck_3992_ == 0 {
                            v___x_3972_ = v_b_3958_;
                            v_isShared_3973_ = v_isSharedCheck_3992_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3970_);
                            crate::leanh::lean_inc(v_fst_3969_);
                            crate::leanh::lean_dec(v_b_3958_);
                            v___x_3972_ = crate::leanh::lean_box(0);
                            v_isShared_3973_ = v_isSharedCheck_3992_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3958_);
                        v_a_3993_ = crate::leanh::lean_ctor_get(v___x_3967_, 0);
                        v_isSharedCheck_4000_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3967_)) as u8;
                        if v_isSharedCheck_4000_ == 0 {
                            v___x_3995_ = v___x_3967_;
                            v_isShared_3996_ = v_isSharedCheck_4000_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3993_);
                            crate::leanh::lean_dec(v___x_3967_);
                            v___x_3995_ = crate::leanh::lean_box(0);
                            v_isShared_3996_ = v_isSharedCheck_4000_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_ctors_3974_ = crate::leanh::lean_ctor_get(v_a_3968_, 4);
                crate::leanh::lean_inc(v_ctors_3974_);
                crate::leanh::lean_dec(v_a_3968_);
                if v_isShared_3973_ == 0 {
                    v___x_3976_ = v___x_3972_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3991_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_fst_3969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_snd_3970_);
                    v___x_3976_ = v_reuseFailAlloc_3991_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3977_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg(v___x_3951_, v___x_3952_, v_recFVars_3953_, v_a_3966_, v_declName_3954_, v_ctors_3974_, v___x_3976_);
                crate::leanh::lean_dec(v_ctors_3974_);
                if crate::leanh::lean_obj_tag(v___x_3977_) == 0 {
                    v_a_3978_ = crate::leanh::lean_ctor_get(v___x_3977_, 0);
                    crate::leanh::lean_inc(v_a_3978_);
                    crate::leanh::lean_dec_ref_known(v___x_3977_, 1);
                    v_fst_3979_ = crate::leanh::lean_ctor_get(v_a_3978_, 0);
                    v_snd_3980_ = crate::leanh::lean_ctor_get(v_a_3978_, 1);
                    v_isSharedCheck_3990_ = (!crate::leanh::lean_is_exclusive(v_a_3978_)) as u8;
                    if v_isSharedCheck_3990_ == 0 {
                        v___x_3982_ = v_a_3978_;
                        v_isShared_3983_ = v_isSharedCheck_3990_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3980_);
                        crate::leanh::lean_inc(v_fst_3979_);
                        crate::leanh::lean_dec(v_a_3978_);
                        v___x_3982_ = crate::leanh::lean_box(0);
                        v_isShared_3983_ = v_isSharedCheck_3990_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_3977_;
                }
            }
            3 => {
                if v_isShared_3983_ == 0 {
                    v___x_3985_ = v___x_3982_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3989_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_fst_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_snd_3980_);
                    v___x_3985_ = v_reuseFailAlloc_3989_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3986_ = 1usize;
                v___x_3987_ = lean_usize_add(v_i_3957_, v___x_3986_);
                v_i_3957_ = v___x_3987_;
                v_b_3958_ = v___x_3985_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3996_ == 0 {
                    v___x_3998_ = v___x_3995_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
                    v___x_3998_ = v_reuseFailAlloc_3999_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__9___boxed(
    mut v___x_4001_: *mut crate::leanh::LeanObject,
    mut v___x_4002_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4003_: *mut crate::leanh::LeanObject,
    mut v_declName_4004_: *mut crate::leanh::LeanObject,
    mut v_as_4005_: *mut crate::leanh::LeanObject,
    mut v_sz_4006_: *mut crate::leanh::LeanObject,
    mut v_i_4007_: *mut crate::leanh::LeanObject,
    mut v_b_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4014_: usize = 0;
    let mut v_i_boxed_4015_: usize = 0;
    let mut v_res_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4014_ = crate::leanh::lean_unbox_usize(v_sz_4006_);
    crate::leanh::lean_dec(v_sz_4006_);
    v_i_boxed_4015_ = crate::leanh::lean_unbox_usize(v_i_4007_);
    crate::leanh::lean_dec(v_i_4007_);
    v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__9(v___x_4001_, v___x_4002_, v_recFVars_4003_, v_declName_4004_, v_as_4005_, v_sz_boxed_4014_, v_i_boxed_4015_, v_b_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
    crate::leanh::lean_dec(v___y_4012_);
    crate::leanh::lean_dec_ref(v___y_4011_);
    crate::leanh::lean_dec(v___y_4010_);
    crate::leanh::lean_dec_ref(v___y_4009_);
    crate::leanh::lean_dec_ref(v_as_4005_);
    crate::leanh::lean_dec(v_declName_4004_);
    crate::leanh::lean_dec_ref(v_recFVars_4003_);
    crate::leanh::lean_dec(v___x_4002_);
    crate::leanh::lean_dec(v___x_4001_);
    return v_res_4016_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg(
    mut v___x_4017_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4018_: *mut crate::leanh::LeanObject,
    mut v___x_4019_: *mut crate::leanh::LeanObject,
    mut v___x_4020_: *mut crate::leanh::LeanObject,
    mut v_declName_4021_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4022_: *mut crate::leanh::LeanObject,
    mut v_b_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
    mut v___y_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v_fst_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v_fst_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4053_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4072_: u8 = 0;
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4076_: u8 = 0;
    let mut v_a_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4080_: u8 = 0;
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4084_: u8 = 0;
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: u8 = 0;
    let mut v_isSharedCheck_4103_: u8 = 0;
    let mut v_isSharedCheck_4104_: u8 = 0;
    let mut v_unused_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v_unused_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4022_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_4019_);
                    v___x_4029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4029_, 0, v_b_4023_);
                    return v___x_4029_;
                } else {
                    v_snd_4030_ = crate::leanh::lean_ctor_get(v_b_4023_, 1);
                    crate::leanh::lean_inc(v_snd_4030_);
                    v_snd_4031_ = crate::leanh::lean_ctor_get(v_snd_4030_, 1);
                    crate::leanh::lean_inc(v_snd_4031_);
                    v_head_4032_ = crate::leanh::lean_ctor_get(v_as_x27_4022_, 0);
                    v_tail_4033_ = crate::leanh::lean_ctor_get(v_as_x27_4022_, 1);
                    v_fst_4034_ = crate::leanh::lean_ctor_get(v_b_4023_, 0);
                    v_isSharedCheck_4106_ = (!crate::leanh::lean_is_exclusive(v_b_4023_)) as u8;
                    if v_isSharedCheck_4106_ == 0 {
                        v_unused_4107_ = crate::leanh::lean_ctor_get(v_b_4023_, 1);
                        crate::leanh::lean_dec(v_unused_4107_);
                        v___x_4036_ = v_b_4023_;
                        v_isShared_4037_ = v_isSharedCheck_4106_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4034_);
                        crate::leanh::lean_dec(v_b_4023_);
                        v___x_4036_ = crate::leanh::lean_box(0);
                        v_isShared_4037_ = v_isSharedCheck_4106_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4038_ = crate::leanh::lean_ctor_get(v_snd_4030_, 0);
                v_isSharedCheck_4104_ = (!crate::leanh::lean_is_exclusive(v_snd_4030_)) as u8;
                if v_isSharedCheck_4104_ == 0 {
                    v_unused_4105_ = crate::leanh::lean_ctor_get(v_snd_4030_, 1);
                    crate::leanh::lean_dec(v_unused_4105_);
                    v___x_4040_ = v_snd_4030_;
                    v_isShared_4041_ = v_isSharedCheck_4104_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4038_);
                    crate::leanh::lean_dec(v_snd_4030_);
                    v___x_4040_ = crate::leanh::lean_box(0);
                    v_isShared_4041_ = v_isSharedCheck_4104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_4042_ = crate::leanh::lean_ctor_get(v_snd_4031_, 0);
                v_snd_4043_ = crate::leanh::lean_ctor_get(v_snd_4031_, 1);
                v_isSharedCheck_4103_ = (!crate::leanh::lean_is_exclusive(v_snd_4031_)) as u8;
                if v_isSharedCheck_4103_ == 0 {
                    v___x_4045_ = v_snd_4031_;
                    v_isShared_4046_ = v_isSharedCheck_4103_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4043_);
                    crate::leanh::lean_inc(v_fst_4042_);
                    crate::leanh::lean_dec(v_snd_4031_);
                    v___x_4045_ = crate::leanh::lean_box(0);
                    v_isShared_4046_ = v_isSharedCheck_4103_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4047_ = l_Lean_instInhabitedExpr;
                v___x_4048_ = lean_nat_add(v___x_4017_, v_head_4032_);
                v___x_4049_ = lean_array_get_borrowed(v___x_4047_, v_recFVars_4018_, v___x_4048_);
                crate::leanh::lean_dec(v___x_4048_);
                v___x_4050_ = l_Lean_Expr_fvarId_x21(v___x_4049_);
                crate::leanh::lean_inc(v___x_4050_);
                v___x_4051_ = lean_array_push(v_fst_4042_, v___x_4050_);
                v___x_4098_ = lean_array_get_size(v___x_4020_);
                v___x_4099_ = lean_nat_dec_lt(v_head_4032_, v___x_4098_);
                if v___x_4099_ == 0 {
                    v___y_4053_ = v___x_4099_;
                    state = 4;
                    continue;
                } else {
                    v___x_4100_ = crate::leanh::lean_box(0);
                    v___x_4101_ = lean_array_get_borrowed(v___x_4100_, v___x_4020_, v_head_4032_);
                    v___x_4102_ = lean_name_eq(v___x_4101_, v_declName_4021_);
                    v___y_4053_ = v___x_4102_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_4053_ == 0 {
                    crate::leanh::lean_dec(v___x_4050_);
                    crate::leanh::lean_inc(v___y_4027_);
                    crate::leanh::lean_inc_ref(v___y_4026_);
                    crate::leanh::lean_inc(v___y_4025_);
                    crate::leanh::lean_inc_ref(v___y_4024_);
                    crate::leanh::lean_inc(v___x_4049_);
                    v___x_4054_ = lean_infer_type(
                        v___x_4049_,
                        v___y_4024_,
                        v___y_4025_,
                        v___y_4026_,
                        v___y_4027_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4054_) == 0 {
                        v_a_4055_ = crate::leanh::lean_ctor_get(v___x_4054_, 0);
                        crate::leanh::lean_inc(v_a_4055_);
                        crate::leanh::lean_dec_ref_known(v___x_4054_, 1);
                        crate::leanh::lean_inc_ref(v___x_4019_);
                        v___x_4056_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnFunUnit(v_a_4055_, v___x_4019_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                        if crate::leanh::lean_obj_tag(v___x_4056_) == 0 {
                            v_a_4057_ = crate::leanh::lean_ctor_get(v___x_4056_, 0);
                            crate::leanh::lean_inc(v_a_4057_);
                            crate::leanh::lean_dec_ref_known(v___x_4056_, 1);
                            v___x_4058_ = lean_array_push(v_fst_4038_, v_a_4057_);
                            if v_isShared_4046_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4051_);
                                v___x_4060_ = v___x_4045_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_4068_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4051_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_snd_4043_);
                                v___x_4060_ = v_reuseFailAlloc_4068_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4051_);
                            crate::leanh::lean_del_object(v___x_4045_);
                            crate::leanh::lean_dec(v_snd_4043_);
                            crate::leanh::lean_del_object(v___x_4040_);
                            crate::leanh::lean_dec(v_fst_4038_);
                            crate::leanh::lean_del_object(v___x_4036_);
                            crate::leanh::lean_dec(v_fst_4034_);
                            crate::leanh::lean_dec_ref(v___x_4019_);
                            v_a_4069_ = crate::leanh::lean_ctor_get(v___x_4056_, 0);
                            v_isSharedCheck_4076_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4056_)) as u8;
                            if v_isSharedCheck_4076_ == 0 {
                                v___x_4071_ = v___x_4056_;
                                v_isShared_4072_ = v_isSharedCheck_4076_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4069_);
                                crate::leanh::lean_dec(v___x_4056_);
                                v___x_4071_ = crate::leanh::lean_box(0);
                                v_isShared_4072_ = v_isSharedCheck_4076_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4051_);
                        crate::leanh::lean_del_object(v___x_4045_);
                        crate::leanh::lean_dec(v_snd_4043_);
                        crate::leanh::lean_del_object(v___x_4040_);
                        crate::leanh::lean_dec(v_fst_4038_);
                        crate::leanh::lean_del_object(v___x_4036_);
                        crate::leanh::lean_dec(v_fst_4034_);
                        crate::leanh::lean_dec_ref(v___x_4019_);
                        v_a_4077_ = crate::leanh::lean_ctor_get(v___x_4054_, 0);
                        v_isSharedCheck_4084_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4054_)) as u8;
                        if v_isSharedCheck_4084_ == 0 {
                            v___x_4079_ = v___x_4054_;
                            v_isShared_4080_ = v_isSharedCheck_4084_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4077_);
                            crate::leanh::lean_dec(v___x_4054_);
                            v___x_4079_ = crate::leanh::lean_box(0);
                            v_isShared_4080_ = v_isSharedCheck_4084_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_4043_);
                    crate::leanh::lean_inc_n(v___x_4049_, 2);
                    v___x_4085_ = lean_array_push(v_fst_4034_, v___x_4049_);
                    v___x_4086_ = lean_array_push(v_fst_4038_, v___x_4049_);
                    v___x_4087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4087_, 0, v___x_4050_);
                    if v_isShared_4046_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4045_, 1, v___x_4087_);
                        crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4051_);
                        v___x_4089_ = v___x_4045_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4051_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 1, v___x_4087_);
                        v___x_4089_ = v_reuseFailAlloc_4097_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4040_, 1, v___x_4060_);
                    crate::leanh::lean_ctor_set(v___x_4040_, 0, v___x_4058_);
                    v___x_4062_ = v___x_4040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4067_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 1, v___x_4060_);
                    v___x_4062_ = v_reuseFailAlloc_4067_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4036_, 1, v___x_4062_);
                    v___x_4064_ = v___x_4036_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_fst_4034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4062_);
                    v___x_4064_ = v_reuseFailAlloc_4066_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_as_x27_4022_ = v_tail_4033_;
                v_b_4023_ = v___x_4064_;
                state = 0;
                continue;
            }
            8 => {
                if v_isShared_4072_ == 0 {
                    v___x_4074_ = v___x_4071_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
                    v___x_4074_ = v_reuseFailAlloc_4075_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4074_;
            }
            10 => {
                if v_isShared_4080_ == 0 {
                    v___x_4082_ = v___x_4079_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
                    v___x_4082_ = v_reuseFailAlloc_4083_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4082_;
            }
            12 => {
                if v_isShared_4041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4040_, 1, v___x_4089_);
                    crate::leanh::lean_ctor_set(v___x_4040_, 0, v___x_4086_);
                    v___x_4091_ = v___x_4040_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4089_);
                    v___x_4091_ = v_reuseFailAlloc_4096_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4036_, 1, v___x_4091_);
                    crate::leanh::lean_ctor_set(v___x_4036_, 0, v___x_4085_);
                    v___x_4093_ = v___x_4036_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4095_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4091_);
                    v___x_4093_ = v_reuseFailAlloc_4095_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v_as_x27_4022_ = v_tail_4033_;
                v_b_4023_ = v___x_4093_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg___boxed(
    mut v___x_4108_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4109_: *mut crate::leanh::LeanObject,
    mut v___x_4110_: *mut crate::leanh::LeanObject,
    mut v___x_4111_: *mut crate::leanh::LeanObject,
    mut v_declName_4112_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4113_: *mut crate::leanh::LeanObject,
    mut v_b_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4120_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg(v___x_4108_, v_recFVars_4109_, v___x_4110_, v___x_4111_, v_declName_4112_, v_as_x27_4113_, v_b_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
    crate::leanh::lean_dec(v___y_4118_);
    crate::leanh::lean_dec_ref(v___y_4117_);
    crate::leanh::lean_dec(v___y_4116_);
    crate::leanh::lean_dec_ref(v___y_4115_);
    crate::leanh::lean_dec(v_as_x27_4113_);
    crate::leanh::lean_dec(v_declName_4112_);
    crate::leanh::lean_dec_ref(v___x_4111_);
    crate::leanh::lean_dec_ref(v_recFVars_4109_);
    crate::leanh::lean_dec(v___x_4108_);
    return v_res_4120_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg(
    mut v_recFVars_4121_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4122_: *mut crate::leanh::LeanObject,
    mut v_b_4123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4122_) == 0 {
                    v___x_4125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4125_, 0, v_b_4123_);
                    return v___x_4125_;
                } else {
                    v_head_4126_ = crate::leanh::lean_ctor_get(v_as_x27_4122_, 0);
                    v_tail_4127_ = crate::leanh::lean_ctor_get(v_as_x27_4122_, 1);
                    v_fst_4128_ = crate::leanh::lean_ctor_get(v_b_4123_, 0);
                    v_snd_4129_ = crate::leanh::lean_ctor_get(v_b_4123_, 1);
                    v_isSharedCheck_4141_ = (!crate::leanh::lean_is_exclusive(v_b_4123_)) as u8;
                    if v_isSharedCheck_4141_ == 0 {
                        v___x_4131_ = v_b_4123_;
                        v_isShared_4132_ = v_isSharedCheck_4141_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4129_);
                        crate::leanh::lean_inc(v_fst_4128_);
                        crate::leanh::lean_dec(v_b_4123_);
                        v___x_4131_ = crate::leanh::lean_box(0);
                        v_isShared_4132_ = v_isSharedCheck_4141_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4133_ = l_Lean_instInhabitedExpr;
                v___x_4134_ = lean_array_get_borrowed(v___x_4133_, v_recFVars_4121_, v_head_4126_);
                crate::leanh::lean_inc_n(v___x_4134_, 2);
                v___x_4135_ = lean_array_push(v_fst_4128_, v___x_4134_);
                v___x_4136_ = lean_array_push(v_snd_4129_, v___x_4134_);
                if v_isShared_4132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4131_, 1, v___x_4136_);
                    crate::leanh::lean_ctor_set(v___x_4131_, 0, v___x_4135_);
                    v___x_4138_ = v___x_4131_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 1, v___x_4136_);
                    v___x_4138_ = v_reuseFailAlloc_4140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_as_x27_4122_ = v_tail_4127_;
                v_b_4123_ = v___x_4138_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg___boxed(
    mut v_recFVars_4142_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4143_: *mut crate::leanh::LeanObject,
    mut v_b_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4146_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg(v_recFVars_4142_, v_as_x27_4143_, v_b_4144_);
    crate::leanh::lean_dec(v_as_x27_4143_);
    crate::leanh::lean_dec_ref(v_recFVars_4142_);
    return v_res_4146_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__3;
    v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__5;
    v___x_4160_ = l_Lean_stringToMessageData(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4162_ =
        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__7;
    v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
    return v___x_4163_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1(
    mut v_numParams_4164_: *mut crate::leanh::LeanObject,
    mut v_numMotives_4165_: *mut crate::leanh::LeanObject,
    mut v___x_4166_: *mut crate::leanh::LeanObject,
    mut v___x_4167_: *mut crate::leanh::LeanObject,
    mut v_declName_4168_: *mut crate::leanh::LeanObject,
    mut v_numIndices_4169_: *mut crate::leanh::LeanObject,
    mut v_numMinors_4170_: *mut crate::leanh::LeanObject,
    mut v___x_4171_: u8,
    mut v___x_4172_: *mut crate::leanh::LeanObject,
    mut v___x_4173_: *mut crate::leanh::LeanObject,
    mut v___x_4174_: *mut crate::leanh::LeanObject,
    mut v___x_4175_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4176_: *mut crate::leanh::LeanObject,
    mut v_recType_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4213_: usize = 0;
    let mut v___x_4214_: usize = 0;
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4221_: u8 = 0;
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_a_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4237_: u8 = 0;
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4244_: u8 = 0;
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4269_: u8 = 0;
    let mut v_unused_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_unused_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4275_: u8 = 0;
    let mut v_unused_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4281_: u8 = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4285_: u8 = 0;
    let mut v_reuseFailAlloc_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4183_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc(v_numParams_4164_);
                v___x_4184_ = l_List_range(v_numParams_4164_);
                v___x_4185_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__0;
                v___x_4186_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg(v_recFVars_4176_, v___x_4184_, v___x_4185_);
                crate::leanh::lean_dec(v___x_4184_);
                v_a_4187_ = crate::leanh::lean_ctor_get(v___x_4186_, 0);
                crate::leanh::lean_inc(v_a_4187_);
                crate::leanh::lean_dec_ref(v___x_4186_);
                v_fst_4188_ = crate::leanh::lean_ctor_get(v_a_4187_, 0);
                v_snd_4189_ = crate::leanh::lean_ctor_get(v_a_4187_, 1);
                v_isSharedCheck_4287_ = (!crate::leanh::lean_is_exclusive(v_a_4187_)) as u8;
                if v_isSharedCheck_4287_ == 0 {
                    v___x_4191_ = v_a_4187_;
                    v_isShared_4192_ = v_isSharedCheck_4287_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4189_);
                    crate::leanh::lean_inc(v_fst_4188_);
                    crate::leanh::lean_dec(v_a_4187_);
                    v___x_4191_ = crate::leanh::lean_box(0);
                    v_isShared_4192_ = v_isSharedCheck_4287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_numMotives_4165_);
                v___x_4193_ = l_List_range(v_numMotives_4165_);
                v___x_4194_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__1;
                if v_isShared_4192_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4191_, 1, v___x_4194_);
                    crate::leanh::lean_ctor_set(v___x_4191_, 0, v_snd_4189_);
                    v___x_4196_ = v___x_4191_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4286_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_snd_4189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4286_, 1, v___x_4194_);
                    v___x_4196_ = v_reuseFailAlloc_4286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4197_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4197_, 0, v_fst_4188_);
                crate::leanh::lean_ctor_set(v___x_4197_, 1, v___x_4196_);
                crate::leanh::lean_inc_ref(v___x_4166_);
                v___x_4198_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg(v_numParams_4164_, v_recFVars_4176_, v___x_4166_, v___x_4167_, v_declName_4168_, v___x_4193_, v___x_4197_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
                crate::leanh::lean_dec(v___x_4193_);
                if crate::leanh::lean_obj_tag(v___x_4198_) == 0 {
                    v_a_4199_ = crate::leanh::lean_ctor_get(v___x_4198_, 0);
                    crate::leanh::lean_inc(v_a_4199_);
                    crate::leanh::lean_dec_ref_known(v___x_4198_, 1);
                    v_snd_4200_ = crate::leanh::lean_ctor_get(v_a_4199_, 1);
                    crate::leanh::lean_inc(v_snd_4200_);
                    v_snd_4201_ = crate::leanh::lean_ctor_get(v_snd_4200_, 1);
                    crate::leanh::lean_inc(v_snd_4201_);
                    v_snd_4202_ = crate::leanh::lean_ctor_get(v_snd_4201_, 1);
                    if crate::leanh::lean_obj_tag(v_snd_4202_) == 1 {
                        crate::leanh::lean_inc_ref(v_snd_4202_);
                        v_fst_4203_ = crate::leanh::lean_ctor_get(v_a_4199_, 0);
                        crate::leanh::lean_inc(v_fst_4203_);
                        crate::leanh::lean_dec(v_a_4199_);
                        v_fst_4204_ = crate::leanh::lean_ctor_get(v_snd_4200_, 0);
                        crate::leanh::lean_inc(v_fst_4204_);
                        crate::leanh::lean_dec(v_snd_4200_);
                        v_fst_4205_ = crate::leanh::lean_ctor_get(v_snd_4201_, 0);
                        crate::leanh::lean_inc(v_fst_4205_);
                        crate::leanh::lean_dec(v_snd_4201_);
                        v_val_4206_ = crate::leanh::lean_ctor_get(v_snd_4202_, 0);
                        crate::leanh::lean_inc(v_val_4206_);
                        crate::leanh::lean_dec_ref_known(v_snd_4202_, 1);
                        v___x_4207_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4208_ = lean_nat_add(v_numIndices_4169_, v___x_4207_);
                        v___x_4209_ = l_List_range(v___x_4208_);
                        v___x_4210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(v_numParams_4164_, v_numMotives_4165_, v_numMinors_4170_, v_recFVars_4176_, v___x_4209_, v_fst_4203_);
                        v_a_4211_ = crate::leanh::lean_ctor_get(v___x_4210_, 0);
                        crate::leanh::lean_inc(v_a_4211_);
                        crate::leanh::lean_dec_ref(v___x_4210_);
                        v___x_4212_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__2;
                        v_sz_4213_ = lean_array_size(v___x_4167_);
                        v___x_4214_ = 0usize;
                        v___x_4215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__9(v_numParams_4164_, v_numMotives_4165_, v_recFVars_4176_, v_declName_4168_, v___x_4167_, v_sz_4213_, v___x_4214_, v___x_4212_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
                        crate::leanh::lean_dec(v_declName_4168_);
                        if crate::leanh::lean_obj_tag(v___x_4215_) == 0 {
                            v_a_4216_ = crate::leanh::lean_ctor_get(v___x_4215_, 0);
                            crate::leanh::lean_inc(v_a_4216_);
                            crate::leanh::lean_dec_ref_known(v___x_4215_, 1);
                            v_fst_4217_ = crate::leanh::lean_ctor_get(v_a_4216_, 0);
                            v_snd_4218_ = crate::leanh::lean_ctor_get(v_a_4216_, 1);
                            v_isSharedCheck_4233_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4216_)) as u8;
                            if v_isSharedCheck_4233_ == 0 {
                                v___x_4220_ = v_a_4216_;
                                v_isShared_4221_ = v_isSharedCheck_4233_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_4218_);
                                crate::leanh::lean_inc(v_fst_4217_);
                                crate::leanh::lean_dec(v_a_4216_);
                                v___x_4220_ = crate::leanh::lean_box(0);
                                v_isShared_4221_ = v_isSharedCheck_4233_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4211_);
                            crate::leanh::lean_dec(v___x_4209_);
                            crate::leanh::lean_dec(v_val_4206_);
                            crate::leanh::lean_dec(v_fst_4205_);
                            crate::leanh::lean_dec(v_fst_4204_);
                            crate::leanh::lean_dec_ref(v_recType_4177_);
                            crate::leanh::lean_dec_ref(v_recFVars_4176_);
                            crate::leanh::lean_dec_ref(v___x_4175_);
                            crate::leanh::lean_dec(v___x_4174_);
                            crate::leanh::lean_dec(v___x_4173_);
                            crate::leanh::lean_dec_ref(v___x_4172_);
                            crate::leanh::lean_dec(v_numMinors_4170_);
                            crate::leanh::lean_dec_ref(v___x_4166_);
                            crate::leanh::lean_dec(v_numMotives_4165_);
                            crate::leanh::lean_dec(v_numParams_4164_);
                            v_a_4234_ = crate::leanh::lean_ctor_get(v___x_4215_, 0);
                            v_isSharedCheck_4241_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4215_)) as u8;
                            if v_isSharedCheck_4241_ == 0 {
                                v___x_4236_ = v___x_4215_;
                                v_isShared_4237_ = v_isSharedCheck_4241_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4234_);
                                crate::leanh::lean_dec(v___x_4215_);
                                v___x_4236_ = crate::leanh::lean_box(0);
                                v_isShared_4237_ = v_isSharedCheck_4241_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_recType_4177_);
                        crate::leanh::lean_dec_ref(v_recFVars_4176_);
                        crate::leanh::lean_dec_ref(v___x_4175_);
                        crate::leanh::lean_dec(v___x_4174_);
                        crate::leanh::lean_dec(v___x_4173_);
                        crate::leanh::lean_dec_ref(v___x_4172_);
                        crate::leanh::lean_dec(v_numMinors_4170_);
                        crate::leanh::lean_dec_ref(v___x_4166_);
                        crate::leanh::lean_dec(v_numMotives_4165_);
                        crate::leanh::lean_dec(v_numParams_4164_);
                        v_isSharedCheck_4275_ = (!crate::leanh::lean_is_exclusive(v_a_4199_)) as u8;
                        if v_isSharedCheck_4275_ == 0 {
                            v_unused_4276_ = crate::leanh::lean_ctor_get(v_a_4199_, 1);
                            crate::leanh::lean_dec(v_unused_4276_);
                            v_unused_4277_ = crate::leanh::lean_ctor_get(v_a_4199_, 0);
                            crate::leanh::lean_dec(v_unused_4277_);
                            v___x_4243_ = v_a_4199_;
                            v_isShared_4244_ = v_isSharedCheck_4275_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4199_);
                            v___x_4243_ = crate::leanh::lean_box(0);
                            v_isShared_4244_ = v_isSharedCheck_4275_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_recType_4177_);
                    crate::leanh::lean_dec_ref(v_recFVars_4176_);
                    crate::leanh::lean_dec_ref(v___x_4175_);
                    crate::leanh::lean_dec(v___x_4174_);
                    crate::leanh::lean_dec(v___x_4173_);
                    crate::leanh::lean_dec_ref(v___x_4172_);
                    crate::leanh::lean_dec(v_numMinors_4170_);
                    crate::leanh::lean_dec(v_declName_4168_);
                    crate::leanh::lean_dec_ref(v___x_4166_);
                    crate::leanh::lean_dec(v_numMotives_4165_);
                    crate::leanh::lean_dec(v_numParams_4164_);
                    v_a_4278_ = crate::leanh::lean_ctor_get(v___x_4198_, 0);
                    v_isSharedCheck_4285_ = (!crate::leanh::lean_is_exclusive(v___x_4198_)) as u8;
                    if v_isSharedCheck_4285_ == 0 {
                        v___x_4280_ = v___x_4198_;
                        v_isShared_4281_ = v_isSharedCheck_4285_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4278_);
                        crate::leanh::lean_dec(v___x_4198_);
                        v___x_4280_ = crate::leanh::lean_box(0);
                        v_isShared_4281_ = v_isSharedCheck_4285_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4222_ = lean_nat_sub(v_numMinors_4170_, v_snd_4218_);
                v___x_4223_ = l_List_range(v___x_4222_);
                if v_isShared_4221_ == 0 {
                    v___x_4225_ = v___x_4220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_fst_4217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_snd_4218_);
                    v___x_4225_ = v_reuseFailAlloc_4232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4226_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg(v_numParams_4164_, v_numMotives_4165_, v_recFVars_4176_, v___x_4223_, v___x_4225_);
                crate::leanh::lean_dec(v___x_4223_);
                v_a_4227_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
                crate::leanh::lean_inc(v_a_4227_);
                crate::leanh::lean_dec_ref(v___x_4226_);
                v_fst_4228_ = crate::leanh::lean_ctor_get(v_a_4227_, 0);
                crate::leanh::lean_inc(v_fst_4228_);
                crate::leanh::lean_dec(v_a_4227_);
                v___x_4229_ = crate::leanh::lean_box((v___x_4171_) as usize);
                v___f_4230_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__0___boxed as *mut core::ffi::c_void, 17, 10);
                crate::leanh::lean_closure_set(v___f_4230_, 0, v_numParams_4164_);
                crate::leanh::lean_closure_set(v___f_4230_, 1, v_numMotives_4165_);
                crate::leanh::lean_closure_set(v___f_4230_, 2, v_numMinors_4170_);
                crate::leanh::lean_closure_set(v___f_4230_, 3, v_recFVars_4176_);
                crate::leanh::lean_closure_set(v___f_4230_, 4, v___x_4209_);
                crate::leanh::lean_closure_set(v___f_4230_, 5, v_recType_4177_);
                crate::leanh::lean_closure_set(v___f_4230_, 6, v___x_4229_);
                crate::leanh::lean_closure_set(v___f_4230_, 7, v___x_4172_);
                crate::leanh::lean_closure_set(v___f_4230_, 8, v___x_4173_);
                crate::leanh::lean_closure_set(v___f_4230_, 9, v___x_4174_);
                v___x_4231_ =
                    l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_processMinors___redArg(
                        v_fst_4205_,
                        v_val_4206_,
                        v___x_4166_,
                        v___x_4175_,
                        v_fst_4228_,
                        v___x_4183_,
                        v_a_4211_,
                        v_fst_4204_,
                        v___f_4230_,
                        v___y_4178_,
                        v___y_4179_,
                        v___y_4180_,
                        v___y_4181_,
                    );
                return v___x_4231_;
            }
            5 => {
                if v_isShared_4237_ == 0 {
                    v___x_4239_ = v___x_4236_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
                    v___x_4239_ = v_reuseFailAlloc_4240_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4239_;
            }
            7 => {
                v_isSharedCheck_4272_ = (!crate::leanh::lean_is_exclusive(v_snd_4200_)) as u8;
                if v_isSharedCheck_4272_ == 0 {
                    v_unused_4273_ = crate::leanh::lean_ctor_get(v_snd_4200_, 1);
                    crate::leanh::lean_dec(v_unused_4273_);
                    v_unused_4274_ = crate::leanh::lean_ctor_get(v_snd_4200_, 0);
                    crate::leanh::lean_dec(v_unused_4274_);
                    v___x_4246_ = v_snd_4200_;
                    v_isShared_4247_ = v_isSharedCheck_4272_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_4200_);
                    v___x_4246_ = crate::leanh::lean_box(0);
                    v_isShared_4247_ = v_isSharedCheck_4272_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_isSharedCheck_4269_ = (!crate::leanh::lean_is_exclusive(v_snd_4201_)) as u8;
                if v_isSharedCheck_4269_ == 0 {
                    v_unused_4270_ = crate::leanh::lean_ctor_get(v_snd_4201_, 1);
                    crate::leanh::lean_dec(v_unused_4270_);
                    v_unused_4271_ = crate::leanh::lean_ctor_get(v_snd_4201_, 0);
                    crate::leanh::lean_dec(v_unused_4271_);
                    v___x_4249_ = v_snd_4201_;
                    v_isShared_4250_ = v_isSharedCheck_4269_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_4201_);
                    v___x_4249_ = crate::leanh::lean_box(0);
                    v_isShared_4250_ = v_isSharedCheck_4269_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4251_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4_once), _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__4);
                v___x_4252_ = l_Lean_casesOnSuffix;
                crate::leanh::lean_inc(v_declName_4168_);
                v___x_4253_ = l_Lean_Name_str___override(v_declName_4168_, v___x_4252_);
                v___x_4254_ = l_Lean_MessageData_ofName(v___x_4253_);
                if v_isShared_4250_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4249_, 7);
                    crate::leanh::lean_ctor_set(v___x_4249_, 1, v___x_4254_);
                    crate::leanh::lean_ctor_set(v___x_4249_, 0, v___x_4251_);
                    v___x_4256_ = v___x_4249_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4268_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 1, v___x_4254_);
                    v___x_4256_ = v_reuseFailAlloc_4268_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4257_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6_once), _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__6);
                if v_isShared_4247_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4246_, 7);
                    crate::leanh::lean_ctor_set(v___x_4246_, 1, v___x_4257_);
                    crate::leanh::lean_ctor_set(v___x_4246_, 0, v___x_4256_);
                    v___x_4259_ = v___x_4246_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4267_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4267_, 1, v___x_4257_);
                    v___x_4259_ = v_reuseFailAlloc_4267_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4260_ = l_Lean_MessageData_ofName(v_declName_4168_);
                if v_isShared_4244_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4243_, 7);
                    crate::leanh::lean_ctor_set(v___x_4243_, 1, v___x_4260_);
                    crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4259_);
                    v___x_4262_ = v___x_4243_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4266_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4266_, 1, v___x_4260_);
                    v___x_4262_ = v_reuseFailAlloc_4266_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4263_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8_once), _init_l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___closed__8);
                v___x_4264_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4264_, 0, v___x_4262_);
                crate::leanh::lean_ctor_set(v___x_4264_, 1, v___x_4263_);
                v___x_4265_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v___x_4264_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
                return v___x_4265_;
            }
            13 => {
                if v_isShared_4281_ == 0 {
                    v___x_4283_ = v___x_4280_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
                    v___x_4283_ = v_reuseFailAlloc_4284_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numParams_4288_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_numMotives_4289_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4290_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4291_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_declName_4292_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_numIndices_4293_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_numMinors_4294_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_4295_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_4296_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_4297_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_4298_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_4299_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_recFVars_4300_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_recType_4301_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4302_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4303_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4304_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4305_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4306_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_13586__boxed_4307_: u8 = 0;
    let mut v_res_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13586__boxed_4307_ = (crate::leanh::lean_unbox(v___x_4295_) as u8);
    v_res_4308_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1(
        v_numParams_4288_,
        v_numMotives_4289_,
        v___x_4290_,
        v___x_4291_,
        v_declName_4292_,
        v_numIndices_4293_,
        v_numMinors_4294_,
        v___x_13586__boxed_4307_,
        v___x_4296_,
        v___x_4297_,
        v___x_4298_,
        v___x_4299_,
        v_recFVars_4300_,
        v_recType_4301_,
        v___y_4302_,
        v___y_4303_,
        v___y_4304_,
        v___y_4305_,
    );
    crate::leanh::lean_dec(v___y_4305_);
    crate::leanh::lean_dec_ref(v___y_4304_);
    crate::leanh::lean_dec(v___y_4303_);
    crate::leanh::lean_dec_ref(v___y_4302_);
    crate::leanh::lean_dec(v_numIndices_4293_);
    crate::leanh::lean_dec_ref(v___x_4291_);
    return v_res_4308_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg(
    mut v_ref_4309_: *mut crate::leanh::LeanObject,
    mut v_msg_4310_: *mut crate::leanh::LeanObject,
    mut v___y_4311_: *mut crate::leanh::LeanObject,
    mut v___y_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
    mut v___y_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4328_: u8 = 0;
    let mut v_cancelTk_x3f_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4330_: u8 = 0;
    let mut v_inheritedTraceOptions_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4316_ = crate::leanh::lean_ctor_get(v___y_4313_, 0);
    v_fileMap_4317_ = crate::leanh::lean_ctor_get(v___y_4313_, 1);
    v_options_4318_ = crate::leanh::lean_ctor_get(v___y_4313_, 2);
    v_currRecDepth_4319_ = crate::leanh::lean_ctor_get(v___y_4313_, 3);
    v_maxRecDepth_4320_ = crate::leanh::lean_ctor_get(v___y_4313_, 4);
    v_ref_4321_ = crate::leanh::lean_ctor_get(v___y_4313_, 5);
    v_currNamespace_4322_ = crate::leanh::lean_ctor_get(v___y_4313_, 6);
    v_openDecls_4323_ = crate::leanh::lean_ctor_get(v___y_4313_, 7);
    v_initHeartbeats_4324_ = crate::leanh::lean_ctor_get(v___y_4313_, 8);
    v_maxHeartbeats_4325_ = crate::leanh::lean_ctor_get(v___y_4313_, 9);
    v_quotContext_4326_ = crate::leanh::lean_ctor_get(v___y_4313_, 10);
    v_currMacroScope_4327_ = crate::leanh::lean_ctor_get(v___y_4313_, 11);
    v_diag_4328_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4313_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4329_ = crate::leanh::lean_ctor_get(v___y_4313_, 12);
    v_suppressElabErrors_4330_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4313_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4331_ = crate::leanh::lean_ctor_get(v___y_4313_, 13);
    v_ref_4332_ = l_Lean_replaceRef(v_ref_4309_, v_ref_4321_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4331_);
    crate::leanh::lean_inc(v_cancelTk_x3f_4329_);
    crate::leanh::lean_inc(v_currMacroScope_4327_);
    crate::leanh::lean_inc(v_quotContext_4326_);
    crate::leanh::lean_inc(v_maxHeartbeats_4325_);
    crate::leanh::lean_inc(v_initHeartbeats_4324_);
    crate::leanh::lean_inc(v_openDecls_4323_);
    crate::leanh::lean_inc(v_currNamespace_4322_);
    crate::leanh::lean_inc(v_maxRecDepth_4320_);
    crate::leanh::lean_inc(v_currRecDepth_4319_);
    crate::leanh::lean_inc_ref(v_options_4318_);
    crate::leanh::lean_inc_ref(v_fileMap_4317_);
    crate::leanh::lean_inc_ref(v_fileName_4316_);
    v___x_4333_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_4333_, 0, v_fileName_4316_);
    crate::leanh::lean_ctor_set(v___x_4333_, 1, v_fileMap_4317_);
    crate::leanh::lean_ctor_set(v___x_4333_, 2, v_options_4318_);
    crate::leanh::lean_ctor_set(v___x_4333_, 3, v_currRecDepth_4319_);
    crate::leanh::lean_ctor_set(v___x_4333_, 4, v_maxRecDepth_4320_);
    crate::leanh::lean_ctor_set(v___x_4333_, 5, v_ref_4332_);
    crate::leanh::lean_ctor_set(v___x_4333_, 6, v_currNamespace_4322_);
    crate::leanh::lean_ctor_set(v___x_4333_, 7, v_openDecls_4323_);
    crate::leanh::lean_ctor_set(v___x_4333_, 8, v_initHeartbeats_4324_);
    crate::leanh::lean_ctor_set(v___x_4333_, 9, v_maxHeartbeats_4325_);
    crate::leanh::lean_ctor_set(v___x_4333_, 10, v_quotContext_4326_);
    crate::leanh::lean_ctor_set(v___x_4333_, 11, v_currMacroScope_4327_);
    crate::leanh::lean_ctor_set(v___x_4333_, 12, v_cancelTk_x3f_4329_);
    crate::leanh::lean_ctor_set(v___x_4333_, 13, v_inheritedTraceOptions_4331_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4333_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_4328_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4333_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4330_,
    );
    v___x_4334_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v_msg_4310_, v___y_4311_, v___y_4312_, v___x_4333_, v___y_4314_);
    crate::leanh::lean_dec_ref_known(v___x_4333_, 14);
    return v___x_4334_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg___boxed(
    mut v_ref_4335_: *mut crate::leanh::LeanObject,
    mut v_msg_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4342_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg(v_ref_4335_, v_msg_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
    crate::leanh::lean_dec(v___y_4340_);
    crate::leanh::lean_dec_ref(v___y_4339_);
    crate::leanh::lean_dec(v___y_4338_);
    crate::leanh::lean_dec_ref(v___y_4337_);
    crate::leanh::lean_dec(v_ref_4335_);
    return v_res_4342_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4343_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4343_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4344_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__0);
    v___x_4345_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4345_, 0, v___x_4344_);
    return v___x_4345_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1);
    v___x_4347_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4348_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4348_, 0, v___x_4347_);
    crate::leanh::lean_ctor_set(v___x_4348_, 1, v___x_4347_);
    crate::leanh::lean_ctor_set(v___x_4348_, 2, v___x_4347_);
    crate::leanh::lean_ctor_set(v___x_4348_, 3, v___x_4347_);
    crate::leanh::lean_ctor_set(v___x_4348_, 4, v___x_4346_);
    crate::leanh::lean_ctor_set(v___x_4348_, 5, v___x_4346_);
    crate::leanh::lean_ctor_set(v___x_4348_, 6, v___x_4346_);
    crate::leanh::lean_ctor_set(v___x_4348_, 7, v___x_4346_);
    crate::leanh::lean_ctor_set(v___x_4348_, 8, v___x_4346_);
    crate::leanh::lean_ctor_set(v___x_4348_, 9, v___x_4346_);
    return v___x_4348_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4349_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4350_ = lean_mk_empty_array_with_capacity(v___x_4349_);
    v___x_4351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4351_, 0, v___x_4350_);
    return v___x_4351_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4352_: usize = 0;
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4352_ = 5usize;
    v___x_4353_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4354_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4355_ = lean_mk_empty_array_with_capacity(v___x_4354_);
    v___x_4356_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__3);
    v___x_4357_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4356_);
    crate::leanh::lean_ctor_set(v___x_4357_, 1, v___x_4355_);
    crate::leanh::lean_ctor_set(v___x_4357_, 2, v___x_4353_);
    crate::leanh::lean_ctor_set(v___x_4357_, 3, v___x_4353_);
    crate::leanh::lean_ctor_set_usize(v___x_4357_, 4, v___x_4352_);
    return v___x_4357_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4358_ = crate::leanh::lean_box(1);
    v___x_4359_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__4);
    v___x_4360_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__1);
    v___x_4361_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4360_);
    crate::leanh::lean_ctor_set(v___x_4361_, 1, v___x_4359_);
    crate::leanh::lean_ctor_set(v___x_4361_, 2, v___x_4358_);
    return v___x_4361_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4363_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__6;
    v___x_4364_ = l_Lean_stringToMessageData(v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4366_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__8;
    v___x_4367_ = l_Lean_stringToMessageData(v___x_4366_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4369_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__10;
    v___x_4370_ = l_Lean_stringToMessageData(v___x_4369_);
    return v___x_4370_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__12;
    v___x_4373_ = l_Lean_stringToMessageData(v___x_4372_);
    return v___x_4373_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4375_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__14;
    v___x_4376_ = l_Lean_stringToMessageData(v___x_4375_);
    return v___x_4376_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4378_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__16;
    v___x_4379_ = l_Lean_stringToMessageData(v___x_4378_);
    return v___x_4379_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4381_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__18;
    v___x_4382_ = l_Lean_stringToMessageData(v___x_4381_);
    return v___x_4382_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg(
    mut v_msg_4383_: *mut crate::leanh::LeanObject,
    mut v_declHint_4384_: *mut crate::leanh::LeanObject,
    mut v___y_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    let mut v_isExporting_4390_: u8 = 0;
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4412_: u8 = 0;
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4444_: u8 = 0;
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4387_ = lean_st_ref_get(v___y_4385_);
                v_env_4388_ = crate::leanh::lean_ctor_get(v___x_4387_, 0);
                crate::leanh::lean_inc_ref(v_env_4388_);
                crate::leanh::lean_dec(v___x_4387_);
                v___x_4389_ = l_Lean_Name_isAnonymous(v_declHint_4384_);
                if v___x_4389_ == 0 {
                    v_isExporting_4390_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_4388_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4390_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_4388_);
                        crate::leanh::lean_dec(v_declHint_4384_);
                        v___x_4391_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4391_, 0, v_msg_4383_);
                        return v___x_4391_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_4388_);
                        v___x_4392_ = l_Lean_Environment_setExporting(v_env_4388_, v___x_4389_);
                        crate::leanh::lean_inc(v_declHint_4384_);
                        crate::leanh::lean_inc_ref(v___x_4392_);
                        v___x_4393_ = l_Lean_Environment_contains(
                            v___x_4392_,
                            v_declHint_4384_,
                            v_isExporting_4390_,
                        );
                        if v___x_4393_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4392_);
                            crate::leanh::lean_dec_ref(v_env_4388_);
                            crate::leanh::lean_dec(v_declHint_4384_);
                            v___x_4394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4394_, 0, v_msg_4383_);
                            return v___x_4394_;
                        } else {
                            v___x_4395_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__2);
                            v___x_4396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__5);
                            v___x_4397_ = l_Lean_Options_empty;
                            v___x_4398_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4398_, 0, v___x_4392_);
                            crate::leanh::lean_ctor_set(v___x_4398_, 1, v___x_4395_);
                            crate::leanh::lean_ctor_set(v___x_4398_, 2, v___x_4396_);
                            crate::leanh::lean_ctor_set(v___x_4398_, 3, v___x_4397_);
                            crate::leanh::lean_inc(v_declHint_4384_);
                            v___x_4399_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4384_, v___x_4389_);
                            v_c_4400_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_4400_, 0, v___x_4398_);
                            crate::leanh::lean_ctor_set(v_c_4400_, 1, v___x_4399_);
                            v___x_4401_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4388_,
                                v_declHint_4384_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4401_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_4388_);
                                crate::leanh::lean_dec(v_declHint_4384_);
                                v___x_4402_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7);
                                v___x_4403_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4403_, 0, v___x_4402_);
                                crate::leanh::lean_ctor_set(v___x_4403_, 1, v_c_4400_);
                                v___x_4404_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__9);
                                v___x_4405_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4405_, 0, v___x_4403_);
                                crate::leanh::lean_ctor_set(v___x_4405_, 1, v___x_4404_);
                                v___x_4406_ = l_Lean_MessageData_note(v___x_4405_);
                                v___x_4407_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4407_, 0, v_msg_4383_);
                                crate::leanh::lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                                v___x_4408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4408_, 0, v___x_4407_);
                                return v___x_4408_;
                            } else {
                                v_val_4409_ = crate::leanh::lean_ctor_get(v___x_4401_, 0);
                                v_isSharedCheck_4444_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4401_)) as u8;
                                if v_isSharedCheck_4444_ == 0 {
                                    v___x_4411_ = v___x_4401_;
                                    v_isShared_4412_ = v_isSharedCheck_4444_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_4409_);
                                    crate::leanh::lean_dec(v___x_4401_);
                                    v___x_4411_ = crate::leanh::lean_box(0);
                                    v_isShared_4412_ = v_isSharedCheck_4444_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4388_);
                    crate::leanh::lean_dec(v_declHint_4384_);
                    v___x_4445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4445_, 0, v_msg_4383_);
                    return v___x_4445_;
                }
            }
            1 => {
                v___x_4413_ = crate::leanh::lean_box(0);
                v___x_4414_ = l_Lean_Environment_header(v_env_4388_);
                crate::leanh::lean_dec_ref(v_env_4388_);
                v___x_4415_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4414_);
                v_mod_4416_ = lean_array_get(v___x_4413_, v___x_4415_, v_val_4409_);
                crate::leanh::lean_dec(v_val_4409_);
                crate::leanh::lean_dec_ref(v___x_4415_);
                v___x_4417_ = l_Lean_isPrivateName(v_declHint_4384_);
                crate::leanh::lean_dec(v_declHint_4384_);
                if v___x_4417_ == 0 {
                    v___x_4418_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__11);
                    v___x_4419_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4419_, 0, v___x_4418_);
                    crate::leanh::lean_ctor_set(v___x_4419_, 1, v_c_4400_);
                    v___x_4420_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__13);
                    v___x_4421_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4421_, 0, v___x_4419_);
                    crate::leanh::lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                    v___x_4422_ = l_Lean_MessageData_ofName(v_mod_4416_);
                    v___x_4423_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4423_, 0, v___x_4421_);
                    crate::leanh::lean_ctor_set(v___x_4423_, 1, v___x_4422_);
                    v___x_4424_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__15);
                    v___x_4425_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4425_, 0, v___x_4423_);
                    crate::leanh::lean_ctor_set(v___x_4425_, 1, v___x_4424_);
                    v___x_4426_ = l_Lean_MessageData_note(v___x_4425_);
                    v___x_4427_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4427_, 0, v_msg_4383_);
                    crate::leanh::lean_ctor_set(v___x_4427_, 1, v___x_4426_);
                    if v_isShared_4412_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4411_, 0);
                        crate::leanh::lean_ctor_set(v___x_4411_, 0, v___x_4427_);
                        v___x_4429_ = v___x_4411_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4427_);
                        v___x_4429_ = v_reuseFailAlloc_4430_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__7);
                    v___x_4432_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4432_, 0, v___x_4431_);
                    crate::leanh::lean_ctor_set(v___x_4432_, 1, v_c_4400_);
                    v___x_4433_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__17);
                    v___x_4434_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4434_, 0, v___x_4432_);
                    crate::leanh::lean_ctor_set(v___x_4434_, 1, v___x_4433_);
                    v___x_4435_ = l_Lean_MessageData_ofName(v_mod_4416_);
                    v___x_4436_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4436_, 0, v___x_4434_);
                    crate::leanh::lean_ctor_set(v___x_4436_, 1, v___x_4435_);
                    v___x_4437_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___closed__19);
                    v___x_4438_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4438_, 0, v___x_4436_);
                    crate::leanh::lean_ctor_set(v___x_4438_, 1, v___x_4437_);
                    v___x_4439_ = l_Lean_MessageData_note(v___x_4438_);
                    v___x_4440_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4440_, 0, v_msg_4383_);
                    crate::leanh::lean_ctor_set(v___x_4440_, 1, v___x_4439_);
                    if v_isShared_4412_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4411_, 0);
                        crate::leanh::lean_ctor_set(v___x_4411_, 0, v___x_4440_);
                        v___x_4442_ = v___x_4411_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 0, v___x_4440_);
                        v___x_4442_ = v_reuseFailAlloc_4443_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4429_;
            }
            3 => {
                return v___x_4442_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg___boxed(
    mut v_msg_4446_: *mut crate::leanh::LeanObject,
    mut v_declHint_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4450_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg(v_msg_4446_, v_declHint_4447_, v___y_4448_);
    crate::leanh::lean_dec(v___y_4448_);
    return v_res_4450_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17(
    mut v_msg_4451_: *mut crate::leanh::LeanObject,
    mut v_declHint_4452_: *mut crate::leanh::LeanObject,
    mut v___y_4453_: *mut crate::leanh::LeanObject,
    mut v___y_4454_: *mut crate::leanh::LeanObject,
    mut v___y_4455_: *mut crate::leanh::LeanObject,
    mut v___y_4456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4458_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg(v_msg_4451_, v_declHint_4452_, v___y_4456_);
                v_a_4459_ = crate::leanh::lean_ctor_get(v___x_4458_, 0);
                v_isSharedCheck_4468_ = (!crate::leanh::lean_is_exclusive(v___x_4458_)) as u8;
                if v_isSharedCheck_4468_ == 0 {
                    v___x_4461_ = v___x_4458_;
                    v_isShared_4462_ = v_isSharedCheck_4468_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4459_);
                    crate::leanh::lean_dec(v___x_4458_);
                    v___x_4461_ = crate::leanh::lean_box(0);
                    v_isShared_4462_ = v_isSharedCheck_4468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4463_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4464_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4464_, 0, v___x_4463_);
                crate::leanh::lean_ctor_set(v___x_4464_, 1, v_a_4459_);
                if v_isShared_4462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4461_, 0, v___x_4464_);
                    v___x_4466_ = v___x_4461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4464_);
                    v___x_4466_ = v_reuseFailAlloc_4467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17___boxed(
    mut v_msg_4469_: *mut crate::leanh::LeanObject,
    mut v_declHint_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
    mut v___y_4472_: *mut crate::leanh::LeanObject,
    mut v___y_4473_: *mut crate::leanh::LeanObject,
    mut v___y_4474_: *mut crate::leanh::LeanObject,
    mut v___y_4475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17(v_msg_4469_, v_declHint_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
    crate::leanh::lean_dec(v___y_4474_);
    crate::leanh::lean_dec_ref(v___y_4473_);
    crate::leanh::lean_dec(v___y_4472_);
    crate::leanh::lean_dec_ref(v___y_4471_);
    return v_res_4476_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg(
    mut v_ref_4477_: *mut crate::leanh::LeanObject,
    mut v_msg_4478_: *mut crate::leanh::LeanObject,
    mut v_declHint_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
    mut v___y_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4485_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17(v_msg_4478_, v_declHint_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
    v_a_4486_ = crate::leanh::lean_ctor_get(v___x_4485_, 0);
    crate::leanh::lean_inc(v_a_4486_);
    crate::leanh::lean_dec_ref(v___x_4485_);
    v___x_4487_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg(v_ref_4477_, v_a_4486_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
    return v___x_4487_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg___boxed(
    mut v_ref_4488_: *mut crate::leanh::LeanObject,
    mut v_msg_4489_: *mut crate::leanh::LeanObject,
    mut v_declHint_4490_: *mut crate::leanh::LeanObject,
    mut v___y_4491_: *mut crate::leanh::LeanObject,
    mut v___y_4492_: *mut crate::leanh::LeanObject,
    mut v___y_4493_: *mut crate::leanh::LeanObject,
    mut v___y_4494_: *mut crate::leanh::LeanObject,
    mut v___y_4495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4496_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg(v_ref_4488_, v_msg_4489_, v_declHint_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
    crate::leanh::lean_dec(v___y_4494_);
    crate::leanh::lean_dec_ref(v___y_4493_);
    crate::leanh::lean_dec(v___y_4492_);
    crate::leanh::lean_dec_ref(v___y_4491_);
    crate::leanh::lean_dec(v_ref_4488_);
    return v_res_4496_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4498_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__0;
    v___x_4499_ = l_Lean_stringToMessageData(v___x_4498_);
    return v___x_4499_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg(
    mut v_ref_4500_: *mut crate::leanh::LeanObject,
    mut v_constName_4501_: *mut crate::leanh::LeanObject,
    mut v___y_4502_: *mut crate::leanh::LeanObject,
    mut v___y_4503_: *mut crate::leanh::LeanObject,
    mut v___y_4504_: *mut crate::leanh::LeanObject,
    mut v___y_4505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: u8 = 0;
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4507_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___closed__1);
    v___x_4508_ = 0;
    crate::leanh::lean_inc(v_constName_4501_);
    v___x_4509_ = l_Lean_MessageData_ofConstName(v_constName_4501_, v___x_4508_);
    v___x_4510_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4510_, 0, v___x_4507_);
    crate::leanh::lean_ctor_set(v___x_4510_, 1, v___x_4509_);
    v___x_4511_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1);
    v___x_4512_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4512_, 0, v___x_4510_);
    crate::leanh::lean_ctor_set(v___x_4512_, 1, v___x_4511_);
    v___x_4513_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg(v_ref_4500_, v___x_4512_, v_constName_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
    return v___x_4513_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_ref_4514_: *mut crate::leanh::LeanObject,
    mut v_constName_4515_: *mut crate::leanh::LeanObject,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4521_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg(v_ref_4514_, v_constName_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
    crate::leanh::lean_dec(v___y_4519_);
    crate::leanh::lean_dec_ref(v___y_4518_);
    crate::leanh::lean_dec(v___y_4517_);
    crate::leanh::lean_dec_ref(v___y_4516_);
    crate::leanh::lean_dec(v_ref_4514_);
    return v_res_4521_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg(
    mut v_constName_4522_: *mut crate::leanh::LeanObject,
    mut v___y_4523_: *mut crate::leanh::LeanObject,
    mut v___y_4524_: *mut crate::leanh::LeanObject,
    mut v___y_4525_: *mut crate::leanh::LeanObject,
    mut v___y_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4528_ = crate::leanh::lean_ctor_get(v___y_4525_, 5);
    v___x_4529_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg(v_ref_4528_, v_constName_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
    return v___x_4529_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg___boxed(
    mut v_constName_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
    mut v___y_4532_: *mut crate::leanh::LeanObject,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4536_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg(v_constName_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
    crate::leanh::lean_dec(v___y_4534_);
    crate::leanh::lean_dec_ref(v___y_4533_);
    crate::leanh::lean_dec(v___y_4532_);
    crate::leanh::lean_dec_ref(v___y_4531_);
    return v_res_4536_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2(
    mut v_constName_4537_: *mut crate::leanh::LeanObject,
    mut v___y_4538_: *mut crate::leanh::LeanObject,
    mut v___y_4539_: *mut crate::leanh::LeanObject,
    mut v___y_4540_: *mut crate::leanh::LeanObject,
    mut v___y_4541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4543_ = lean_st_ref_get(v___y_4541_);
                v_env_4544_ = crate::leanh::lean_ctor_get(v___x_4543_, 0);
                crate::leanh::lean_inc_ref(v_env_4544_);
                crate::leanh::lean_dec(v___x_4543_);
                v___x_4545_ = 0;
                crate::leanh::lean_inc(v_constName_4537_);
                v___x_4546_ =
                    l_Lean_Environment_find_x3f(v_env_4544_, v_constName_4537_, v___x_4545_);
                if crate::leanh::lean_obj_tag(v___x_4546_) == 0 {
                    v___x_4547_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg(v_constName_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
                    return v___x_4547_;
                } else {
                    crate::leanh::lean_dec(v_constName_4537_);
                    v_val_4548_ = crate::leanh::lean_ctor_get(v___x_4546_, 0);
                    v_isSharedCheck_4555_ = (!crate::leanh::lean_is_exclusive(v___x_4546_)) as u8;
                    if v_isSharedCheck_4555_ == 0 {
                        v___x_4550_ = v___x_4546_;
                        v_isShared_4551_ = v_isSharedCheck_4555_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4548_);
                        crate::leanh::lean_dec(v___x_4546_);
                        v___x_4550_ = crate::leanh::lean_box(0);
                        v_isShared_4551_ = v_isSharedCheck_4555_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4551_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4550_, 0);
                    v___x_4553_ = v___x_4550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4554_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_val_4548_);
                    v___x_4553_ = v_reuseFailAlloc_4554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2___boxed(
    mut v_constName_4556_: *mut crate::leanh::LeanObject,
    mut v___y_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
    mut v___y_4561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4562_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2(v_constName_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
    crate::leanh::lean_dec(v___y_4560_);
    crate::leanh::lean_dec_ref(v___y_4559_);
    crate::leanh::lean_dec(v___y_4558_);
    crate::leanh::lean_dec_ref(v___y_4557_);
    return v_res_4562_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__3(
    mut v_a_4563_: *mut crate::leanh::LeanObject,
    mut v_a_4564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4570_: u8 = 0;
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4563_) == 0 {
                    v___x_4565_ = l_List_reverse___redArg(v_a_4564_);
                    return v___x_4565_;
                } else {
                    v_head_4566_ = crate::leanh::lean_ctor_get(v_a_4563_, 0);
                    v_tail_4567_ = crate::leanh::lean_ctor_get(v_a_4563_, 1);
                    v_isSharedCheck_4576_ = (!crate::leanh::lean_is_exclusive(v_a_4563_)) as u8;
                    if v_isSharedCheck_4576_ == 0 {
                        v___x_4569_ = v_a_4563_;
                        v_isShared_4570_ = v_isSharedCheck_4576_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4567_);
                        crate::leanh::lean_inc(v_head_4566_);
                        crate::leanh::lean_dec(v_a_4563_);
                        v___x_4569_ = crate::leanh::lean_box(0);
                        v_isShared_4570_ = v_isSharedCheck_4576_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4571_ = l_Lean_mkLevelParam(v_head_4566_);
                if v_isShared_4570_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4569_, 1, v_a_4564_);
                    crate::leanh::lean_ctor_set(v___x_4569_, 0, v___x_4571_);
                    v___x_4573_ = v___x_4569_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4575_, 0, v___x_4571_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4575_, 1, v_a_4564_);
                    v___x_4573_ = v_reuseFailAlloc_4575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4563_ = v_tail_4567_;
                v_a_4564_ = v___x_4573_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4577_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_4577_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1(
    mut v_msg_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v_toFunctor_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4600_: u8 = 0;
    let mut v___f_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4617_: u8 = 0;
    let mut v_toFunctor_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4624_: u8 = 0;
    let mut v___f_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10082__overap_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4643_: u8 = 0;
    let mut v_unused_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4645_: u8 = 0;
    let mut v_unused_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4649_: u8 = 0;
    let mut v_unused_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut v_unused_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4588_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__0);
                v___x_4589_ = l_StateRefT_x27_instMonad___redArg(v___x_4588_);
                v_toApplicative_4590_ = crate::leanh::lean_ctor_get(v___x_4589_, 0);
                v_isSharedCheck_4651_ = (!crate::leanh::lean_is_exclusive(v___x_4589_)) as u8;
                if v_isSharedCheck_4651_ == 0 {
                    v_unused_4652_ = crate::leanh::lean_ctor_get(v___x_4589_, 1);
                    crate::leanh::lean_dec(v_unused_4652_);
                    v___x_4592_ = v___x_4589_;
                    v_isShared_4593_ = v_isSharedCheck_4651_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4590_);
                    crate::leanh::lean_dec(v___x_4589_);
                    v___x_4592_ = crate::leanh::lean_box(0);
                    v_isShared_4593_ = v_isSharedCheck_4651_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4594_ = crate::leanh::lean_ctor_get(v_toApplicative_4590_, 0);
                v_toSeq_4595_ = crate::leanh::lean_ctor_get(v_toApplicative_4590_, 2);
                v_toSeqLeft_4596_ = crate::leanh::lean_ctor_get(v_toApplicative_4590_, 3);
                v_toSeqRight_4597_ = crate::leanh::lean_ctor_get(v_toApplicative_4590_, 4);
                v_isSharedCheck_4649_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4590_)) as u8;
                if v_isSharedCheck_4649_ == 0 {
                    v_unused_4650_ = crate::leanh::lean_ctor_get(v_toApplicative_4590_, 1);
                    crate::leanh::lean_dec(v_unused_4650_);
                    v___x_4599_ = v_toApplicative_4590_;
                    v_isShared_4600_ = v_isSharedCheck_4649_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4597_);
                    crate::leanh::lean_inc(v_toSeqLeft_4596_);
                    crate::leanh::lean_inc(v_toSeq_4595_);
                    crate::leanh::lean_inc(v_toFunctor_4594_);
                    crate::leanh::lean_dec(v_toApplicative_4590_);
                    v___x_4599_ = crate::leanh::lean_box(0);
                    v_isShared_4600_ = v_isSharedCheck_4649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4601_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__1;
                v___f_4602_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_4594_);
                v___f_4603_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4603_, 0, v_toFunctor_4594_);
                v___f_4604_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4604_, 0, v_toFunctor_4594_);
                v___x_4605_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4605_, 0, v___f_4603_);
                crate::leanh::lean_ctor_set(v___x_4605_, 1, v___f_4604_);
                v___f_4606_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4606_, 0, v_toSeqRight_4597_);
                v___f_4607_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4607_, 0, v_toSeqLeft_4596_);
                v___f_4608_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4608_, 0, v_toSeq_4595_);
                if v_isShared_4600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4599_, 4, v___f_4606_);
                    crate::leanh::lean_ctor_set(v___x_4599_, 3, v___f_4607_);
                    crate::leanh::lean_ctor_set(v___x_4599_, 2, v___f_4608_);
                    crate::leanh::lean_ctor_set(v___x_4599_, 1, v___f_4601_);
                    crate::leanh::lean_ctor_set(v___x_4599_, 0, v___x_4605_);
                    v___x_4610_ = v___x_4599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4648_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 1, v___f_4601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 2, v___f_4608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 3, v___f_4607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 4, v___f_4606_);
                    v___x_4610_ = v_reuseFailAlloc_4648_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4592_, 1, v___f_4602_);
                    crate::leanh::lean_ctor_set(v___x_4592_, 0, v___x_4610_);
                    v___x_4612_ = v___x_4592_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4647_, 1, v___f_4602_);
                    v___x_4612_ = v_reuseFailAlloc_4647_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4613_ = l_StateRefT_x27_instMonad___redArg(v___x_4612_);
                v_toApplicative_4614_ = crate::leanh::lean_ctor_get(v___x_4613_, 0);
                v_isSharedCheck_4645_ = (!crate::leanh::lean_is_exclusive(v___x_4613_)) as u8;
                if v_isSharedCheck_4645_ == 0 {
                    v_unused_4646_ = crate::leanh::lean_ctor_get(v___x_4613_, 1);
                    crate::leanh::lean_dec(v_unused_4646_);
                    v___x_4616_ = v___x_4613_;
                    v_isShared_4617_ = v_isSharedCheck_4645_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4614_);
                    crate::leanh::lean_dec(v___x_4613_);
                    v___x_4616_ = crate::leanh::lean_box(0);
                    v_isShared_4617_ = v_isSharedCheck_4645_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4618_ = crate::leanh::lean_ctor_get(v_toApplicative_4614_, 0);
                v_toSeq_4619_ = crate::leanh::lean_ctor_get(v_toApplicative_4614_, 2);
                v_toSeqLeft_4620_ = crate::leanh::lean_ctor_get(v_toApplicative_4614_, 3);
                v_toSeqRight_4621_ = crate::leanh::lean_ctor_get(v_toApplicative_4614_, 4);
                v_isSharedCheck_4643_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4614_)) as u8;
                if v_isSharedCheck_4643_ == 0 {
                    v_unused_4644_ = crate::leanh::lean_ctor_get(v_toApplicative_4614_, 1);
                    crate::leanh::lean_dec(v_unused_4644_);
                    v___x_4623_ = v_toApplicative_4614_;
                    v_isShared_4624_ = v_isSharedCheck_4643_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4621_);
                    crate::leanh::lean_inc(v_toSeqLeft_4620_);
                    crate::leanh::lean_inc(v_toSeq_4619_);
                    crate::leanh::lean_inc(v_toFunctor_4618_);
                    crate::leanh::lean_dec(v_toApplicative_4614_);
                    v___x_4623_ = crate::leanh::lean_box(0);
                    v_isShared_4624_ = v_isSharedCheck_4643_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4625_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__3;
                v___f_4626_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_4618_);
                v___f_4627_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4627_, 0, v_toFunctor_4618_);
                v___f_4628_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4628_, 0, v_toFunctor_4618_);
                v___x_4629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4629_, 0, v___f_4627_);
                crate::leanh::lean_ctor_set(v___x_4629_, 1, v___f_4628_);
                v___f_4630_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4630_, 0, v_toSeqRight_4621_);
                v___f_4631_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4631_, 0, v_toSeqLeft_4620_);
                v___f_4632_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4632_, 0, v_toSeq_4619_);
                if v_isShared_4624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4623_, 4, v___f_4630_);
                    crate::leanh::lean_ctor_set(v___x_4623_, 3, v___f_4631_);
                    crate::leanh::lean_ctor_set(v___x_4623_, 2, v___f_4632_);
                    crate::leanh::lean_ctor_set(v___x_4623_, 1, v___f_4625_);
                    crate::leanh::lean_ctor_set(v___x_4623_, 0, v___x_4629_);
                    v___x_4634_ = v___x_4623_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4642_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 1, v___f_4625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 2, v___f_4632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 3, v___f_4631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 4, v___f_4630_);
                    v___x_4634_ = v_reuseFailAlloc_4642_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4616_, 1, v___f_4626_);
                    crate::leanh::lean_ctor_set(v___x_4616_, 0, v___x_4634_);
                    v___x_4636_ = v___x_4616_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4641_, 1, v___f_4626_);
                    v___x_4636_ = v_reuseFailAlloc_4641_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4637_ = crate::leanh::lean_box(0);
                v___x_4638_ = l_instInhabitedOfMonad___redArg(v___x_4636_, v___x_4637_);
                v___x_10082__overap_4639_ = lean_panic_fn_borrowed(v___x_4638_, v_msg_4582_);
                crate::leanh::lean_dec(v___x_4638_);
                crate::leanh::lean_inc(v___y_4586_);
                crate::leanh::lean_inc_ref(v___y_4585_);
                crate::leanh::lean_inc(v___y_4584_);
                crate::leanh::lean_inc_ref(v___y_4583_);
                v___x_4640_ = crate::leanh::lean_apply_5(
                    v___x_10082__overap_4639_,
                    v___y_4583_,
                    v___y_4584_,
                    v___y_4585_,
                    v___y_4586_,
                    crate::leanh::lean_box(0),
                );
                return v___x_4640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1___boxed(
    mut v_msg_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1(v_msg_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
    crate::leanh::lean_dec(v___y_4657_);
    crate::leanh::lean_dec_ref(v___y_4656_);
    crate::leanh::lean_dec(v___y_4655_);
    crate::leanh::lean_dec_ref(v___y_4654_);
    return v_res_4659_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__0;
    v___x_4662_ = l_Lean_stringToMessageData(v___x_4661_);
    return v___x_4662_;
}
pub unsafe fn _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4666_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__4;
    v___x_4667_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_4668_ = crate::leanh::lean_unsigned_to_nat(129);
    v___x_4669_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__3;
    v___x_4670_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__2;
    v___x_4671_ = l_mkPanicMessageWithDecl(
        v___x_4670_,
        v___x_4669_,
        v___x_4668_,
        v___x_4667_,
        v___x_4666_,
    );
    return v___x_4671_;
}
pub unsafe fn l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1(
    mut v_constName_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
    mut v___y_4676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: u8 = 0;
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4691_: u8 = 0;
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4696_: u8 = 0;
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v_val_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4711_: u8 = 0;
    let mut v_a_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4715_: u8 = 0;
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4686_ = lean_st_ref_get(v___y_4676_);
                v_env_4687_ = crate::leanh::lean_ctor_get(v___x_4686_, 0);
                crate::leanh::lean_inc_ref(v_env_4687_);
                crate::leanh::lean_dec(v___x_4686_);
                v___x_4688_ = 0;
                crate::leanh::lean_inc(v_constName_4672_);
                v___x_4689_ =
                    l_Lean_Environment_findAsync_x3f(v_env_4687_, v_constName_4672_, v___x_4688_);
                if crate::leanh::lean_obj_tag(v___x_4689_) == 1 {
                    v_val_4690_ = crate::leanh::lean_ctor_get(v___x_4689_, 0);
                    crate::leanh::lean_inc(v_val_4690_);
                    crate::leanh::lean_dec_ref_known(v___x_4689_, 1);
                    v_kind_4691_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_4690_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_4691_ == 7 {
                        v___x_4692_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_4690_);
                        if crate::leanh::lean_obj_tag(v___x_4692_) == 7 {
                            crate::leanh::lean_dec(v_constName_4672_);
                            v_val_4693_ = crate::leanh::lean_ctor_get(v___x_4692_, 0);
                            v_isSharedCheck_4700_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4692_)) as u8;
                            if v_isSharedCheck_4700_ == 0 {
                                v___x_4695_ = v___x_4692_;
                                v_isShared_4696_ = v_isSharedCheck_4700_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_4693_);
                                crate::leanh::lean_dec(v___x_4692_);
                                v___x_4695_ = crate::leanh::lean_box(0);
                                v_isShared_4696_ = v_isSharedCheck_4700_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4692_);
                            v___x_4701_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__5);
                            v___x_4702_ = l_panic___at___00Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1_spec__1(v___x_4701_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
                            if crate::leanh::lean_obj_tag(v___x_4702_) == 0 {
                                v_a_4703_ = crate::leanh::lean_ctor_get(v___x_4702_, 0);
                                v_isSharedCheck_4711_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4702_)) as u8;
                                if v_isSharedCheck_4711_ == 0 {
                                    v___x_4705_ = v___x_4702_;
                                    v_isShared_4706_ = v_isSharedCheck_4711_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4703_);
                                    crate::leanh::lean_dec(v___x_4702_);
                                    v___x_4705_ = crate::leanh::lean_box(0);
                                    v_isShared_4706_ = v_isSharedCheck_4711_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_4672_);
                                v_a_4712_ = crate::leanh::lean_ctor_get(v___x_4702_, 0);
                                v_isSharedCheck_4719_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4702_)) as u8;
                                if v_isSharedCheck_4719_ == 0 {
                                    v___x_4714_ = v___x_4702_;
                                    v_isShared_4715_ = v_isSharedCheck_4719_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4712_);
                                    crate::leanh::lean_dec(v___x_4702_);
                                    v___x_4714_ = crate::leanh::lean_box(0);
                                    v_isShared_4715_ = v_isSharedCheck_4719_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4690_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4689_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4679_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0___closed__1);
                v___x_4680_ = 0;
                v___x_4681_ = l_Lean_MessageData_ofConstName(v_constName_4672_, v___x_4680_);
                v___x_4682_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4682_, 0, v___x_4679_);
                crate::leanh::lean_ctor_set(v___x_4682_, 1, v___x_4681_);
                v___x_4683_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1_once), _init_l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___closed__1);
                v___x_4684_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4684_, 0, v___x_4682_);
                crate::leanh::lean_ctor_set(v___x_4684_, 1, v___x_4683_);
                v___x_4685_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v___x_4684_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
                return v___x_4685_;
            }
            2 => {
                if v_isShared_4696_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4695_, 0);
                    v___x_4698_ = v___x_4695_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4699_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_val_4693_);
                    v___x_4698_ = v_reuseFailAlloc_4699_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4698_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4703_) == 0 {
                    crate::leanh::lean_del_object(v___x_4705_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_4672_);
                    v_val_4707_ = crate::leanh::lean_ctor_get(v_a_4703_, 0);
                    crate::leanh::lean_inc(v_val_4707_);
                    crate::leanh::lean_dec_ref_known(v_a_4703_, 1);
                    if v_isShared_4706_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4705_, 0, v_val_4707_);
                        v___x_4709_ = v___x_4705_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_val_4707_);
                        v___x_4709_ = v_reuseFailAlloc_4710_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4709_;
            }
            6 => {
                if v_isShared_4715_ == 0 {
                    v___x_4717_ = v___x_4714_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4718_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
                    v___x_4717_ = v_reuseFailAlloc_4718_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1___boxed(
    mut v_constName_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
    mut v___y_4722_: *mut crate::leanh::LeanObject,
    mut v___y_4723_: *mut crate::leanh::LeanObject,
    mut v___y_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4726_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1(v_constName_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
    crate::leanh::lean_dec(v___y_4724_);
    crate::leanh::lean_dec_ref(v___y_4723_);
    crate::leanh::lean_dec(v___y_4722_);
    crate::leanh::lean_dec_ref(v___y_4721_);
    return v_res_4726_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(
    mut v_declName_4734_: *mut crate::leanh::LeanObject,
    mut v_a_4735_: *mut crate::leanh::LeanObject,
    mut v_a_4736_: *mut crate::leanh::LeanObject,
    mut v_a_4737_: *mut crate::leanh::LeanObject,
    mut v_a_4738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMotives_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMinors_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: u8 = 0;
    let mut v___x_4762_: u8 = 0;
    let mut v___y_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4782_: u8 = 0;
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4786_: u8 = 0;
    let mut v_a_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4790_: u8 = 0;
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4794_: u8 = 0;
    let mut v_a_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4798_: u8 = 0;
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_4734_);
                v___x_4740_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__0(v_declName_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
                if crate::leanh::lean_obj_tag(v___x_4740_) == 0 {
                    v_a_4741_ = crate::leanh::lean_ctor_get(v___x_4740_, 0);
                    crate::leanh::lean_inc(v_a_4741_);
                    crate::leanh::lean_dec_ref_known(v___x_4740_, 1);
                    crate::leanh::lean_inc_n(v_declName_4734_, 2);
                    v___x_4742_ = l_Lean_mkCasesOnName(v_declName_4734_);
                    v___x_4743_ = l_Lean_mkRecName(v_declName_4734_);
                    crate::leanh::lean_inc(v___x_4743_);
                    v___x_4744_ = l_Lean_getConstInfoRec___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__1(v___x_4743_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
                    if crate::leanh::lean_obj_tag(v___x_4744_) == 0 {
                        v_a_4745_ = crate::leanh::lean_ctor_get(v___x_4744_, 0);
                        crate::leanh::lean_inc(v_a_4745_);
                        crate::leanh::lean_dec_ref_known(v___x_4744_, 1);
                        crate::leanh::lean_inc(v___x_4743_);
                        v___x_4746_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2(v___x_4743_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
                        if crate::leanh::lean_obj_tag(v___x_4746_) == 0 {
                            v_toConstantVal_4747_ = crate::leanh::lean_ctor_get(v_a_4741_, 0);
                            crate::leanh::lean_inc_ref(v_toConstantVal_4747_);
                            crate::leanh::lean_dec(v_a_4741_);
                            v_a_4748_ = crate::leanh::lean_ctor_get(v___x_4746_, 0);
                            crate::leanh::lean_inc(v_a_4748_);
                            crate::leanh::lean_dec_ref_known(v___x_4746_, 1);
                            v_all_4749_ = crate::leanh::lean_ctor_get(v_a_4745_, 1);
                            crate::leanh::lean_inc(v_all_4749_);
                            v_numParams_4750_ = crate::leanh::lean_ctor_get(v_a_4745_, 2);
                            crate::leanh::lean_inc(v_numParams_4750_);
                            v_numIndices_4751_ = crate::leanh::lean_ctor_get(v_a_4745_, 3);
                            crate::leanh::lean_inc(v_numIndices_4751_);
                            v_numMotives_4752_ = crate::leanh::lean_ctor_get(v_a_4745_, 4);
                            crate::leanh::lean_inc(v_numMotives_4752_);
                            v_numMinors_4753_ = crate::leanh::lean_ctor_get(v_a_4745_, 5);
                            crate::leanh::lean_inc(v_numMinors_4753_);
                            crate::leanh::lean_dec(v_a_4745_);
                            v_levelParams_4754_ =
                                crate::leanh::lean_ctor_get(v_toConstantVal_4747_, 1);
                            crate::leanh::lean_inc(v_levelParams_4754_);
                            crate::leanh::lean_dec_ref(v_toConstantVal_4747_);
                            v___x_4755_ = lean_array_mk(v_all_4749_);
                            v___x_4756_ = l_Lean_ConstantInfo_levelParams(v_a_4748_);
                            v___x_4757_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___x_4756_);
                            v___x_4758_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__3(v___x_4756_, v___x_4757_);
                            v___x_4759_ = l_List_lengthTR___redArg(v___x_4756_);
                            v___x_4760_ = l_List_lengthTR___redArg(v_levelParams_4754_);
                            crate::leanh::lean_dec(v_levelParams_4754_);
                            v___x_4761_ = lean_nat_dec_eq(v___x_4759_, v___x_4760_);
                            crate::leanh::lean_dec(v___x_4760_);
                            crate::leanh::lean_dec(v___x_4759_);
                            v___x_4762_ = 1;
                            if v___x_4761_ == 0 {
                                v___x_4776_ = crate::leanh::lean_box(0);
                                v___x_4777_ = l_List_head_x21___redArg(v___x_4776_, v___x_4758_);
                                v___y_4764_ = v___x_4777_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4778_ = crate::leanh::lean_box(0);
                                v___y_4764_ = v___x_4778_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4745_);
                            crate::leanh::lean_dec(v___x_4743_);
                            crate::leanh::lean_dec(v___x_4742_);
                            crate::leanh::lean_dec(v_a_4741_);
                            crate::leanh::lean_dec(v_declName_4734_);
                            v_a_4779_ = crate::leanh::lean_ctor_get(v___x_4746_, 0);
                            v_isSharedCheck_4786_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4746_)) as u8;
                            if v_isSharedCheck_4786_ == 0 {
                                v___x_4781_ = v___x_4746_;
                                v_isShared_4782_ = v_isSharedCheck_4786_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4779_);
                                crate::leanh::lean_dec(v___x_4746_);
                                v___x_4781_ = crate::leanh::lean_box(0);
                                v_isShared_4782_ = v_isSharedCheck_4786_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4743_);
                        crate::leanh::lean_dec(v___x_4742_);
                        crate::leanh::lean_dec(v_a_4741_);
                        crate::leanh::lean_dec(v_declName_4734_);
                        v_a_4787_ = crate::leanh::lean_ctor_get(v___x_4744_, 0);
                        v_isSharedCheck_4794_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4744_)) as u8;
                        if v_isSharedCheck_4794_ == 0 {
                            v___x_4789_ = v___x_4744_;
                            v_isShared_4790_ = v_isSharedCheck_4794_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4787_);
                            crate::leanh::lean_dec(v___x_4744_);
                            v___x_4789_ = crate::leanh::lean_box(0);
                            v_isShared_4790_ = v_isSharedCheck_4794_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_4734_);
                    v_a_4795_ = crate::leanh::lean_ctor_get(v___x_4740_, 0);
                    v_isSharedCheck_4802_ = (!crate::leanh::lean_is_exclusive(v___x_4740_)) as u8;
                    if v_isSharedCheck_4802_ == 0 {
                        v___x_4797_ = v___x_4740_;
                        v_isShared_4798_ = v_isSharedCheck_4802_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4795_);
                        crate::leanh::lean_dec(v___x_4740_);
                        v___x_4797_ = crate::leanh::lean_box(0);
                        v_isShared_4798_ = v_isSharedCheck_4802_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4765_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__1;
                v___x_4766_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4766_, 0, v___y_4764_);
                crate::leanh::lean_ctor_set(v___x_4766_, 1, v___x_4757_);
                crate::leanh::lean_inc_ref(v___x_4766_);
                v___x_4767_ = l_Lean_mkConst(v___x_4765_, v___x_4766_);
                v___x_4768_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___closed__3;
                v___x_4769_ = l_Lean_mkConst(v___x_4768_, v___x_4766_);
                v___x_4770_ = l_Lean_mkConst(v___x_4743_, v___x_4758_);
                v___x_4771_ = crate::leanh::lean_box((v___x_4762_) as usize);
                v___f_4772_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___lam__1___boxed as *mut core::ffi::c_void, 19, 12);
                crate::leanh::lean_closure_set(v___f_4772_, 0, v_numParams_4750_);
                crate::leanh::lean_closure_set(v___f_4772_, 1, v_numMotives_4752_);
                crate::leanh::lean_closure_set(v___f_4772_, 2, v___x_4767_);
                crate::leanh::lean_closure_set(v___f_4772_, 3, v___x_4755_);
                crate::leanh::lean_closure_set(v___f_4772_, 4, v_declName_4734_);
                crate::leanh::lean_closure_set(v___f_4772_, 5, v_numIndices_4751_);
                crate::leanh::lean_closure_set(v___f_4772_, 6, v_numMinors_4753_);
                crate::leanh::lean_closure_set(v___f_4772_, 7, v___x_4771_);
                crate::leanh::lean_closure_set(v___f_4772_, 8, v___x_4770_);
                crate::leanh::lean_closure_set(v___f_4772_, 9, v___x_4742_);
                crate::leanh::lean_closure_set(v___f_4772_, 10, v___x_4756_);
                crate::leanh::lean_closure_set(v___f_4772_, 11, v___x_4769_);
                v___x_4773_ = l_Lean_ConstantInfo_type(v_a_4748_);
                crate::leanh::lean_dec(v_a_4748_);
                v___x_4774_ = 0;
                v___x_4775_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__12___redArg(v___x_4773_, v___f_4772_, v___x_4774_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_);
                return v___x_4775_;
            }
            2 => {
                if v_isShared_4782_ == 0 {
                    v___x_4784_ = v___x_4781_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
                    v___x_4784_ = v_reuseFailAlloc_4785_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4784_;
            }
            4 => {
                if v_isShared_4790_ == 0 {
                    v___x_4792_ = v___x_4789_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
                    v___x_4792_ = v_reuseFailAlloc_4793_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4792_;
            }
            6 => {
                if v_isShared_4798_ == 0 {
                    v___x_4800_ = v___x_4797_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4801_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
                    v___x_4800_ = v_reuseFailAlloc_4801_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl___boxed(
    mut v_declName_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
    mut v_a_4807_: *mut crate::leanh::LeanObject,
    mut v_a_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4809_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(
        v_declName_4803_,
        v_a_4804_,
        v_a_4805_,
        v_a_4806_,
        v_a_4807_,
    );
    crate::leanh::lean_dec(v_a_4807_);
    crate::leanh::lean_dec_ref(v_a_4806_);
    crate::leanh::lean_dec(v_a_4805_);
    crate::leanh::lean_dec_ref(v_a_4804_);
    return v_res_4809_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4(
    mut v_recFVars_4810_: *mut crate::leanh::LeanObject,
    mut v_as_4811_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4812_: *mut crate::leanh::LeanObject,
    mut v_b_4813_: *mut crate::leanh::LeanObject,
    mut v_a_4814_: *mut crate::leanh::LeanObject,
    mut v___y_4815_: *mut crate::leanh::LeanObject,
    mut v___y_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4820_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___redArg(v_recFVars_4810_, v_as_x27_4812_, v_b_4813_);
    return v___x_4820_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4___boxed(
    mut v_recFVars_4821_: *mut crate::leanh::LeanObject,
    mut v_as_4822_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4823_: *mut crate::leanh::LeanObject,
    mut v_b_4824_: *mut crate::leanh::LeanObject,
    mut v_a_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
    mut v___y_4829_: *mut crate::leanh::LeanObject,
    mut v___y_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4831_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__4(v_recFVars_4821_, v_as_4822_, v_as_x27_4823_, v_b_4824_, v_a_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
    crate::leanh::lean_dec(v___y_4829_);
    crate::leanh::lean_dec_ref(v___y_4828_);
    crate::leanh::lean_dec(v___y_4827_);
    crate::leanh::lean_dec_ref(v___y_4826_);
    crate::leanh::lean_dec(v_as_x27_4823_);
    crate::leanh::lean_dec(v_as_4822_);
    crate::leanh::lean_dec_ref(v_recFVars_4821_);
    return v_res_4831_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5(
    mut v___x_4832_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4833_: *mut crate::leanh::LeanObject,
    mut v___x_4834_: *mut crate::leanh::LeanObject,
    mut v___x_4835_: *mut crate::leanh::LeanObject,
    mut v_declName_4836_: *mut crate::leanh::LeanObject,
    mut v_as_4837_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4838_: *mut crate::leanh::LeanObject,
    mut v_b_4839_: *mut crate::leanh::LeanObject,
    mut v_a_4840_: *mut crate::leanh::LeanObject,
    mut v___y_4841_: *mut crate::leanh::LeanObject,
    mut v___y_4842_: *mut crate::leanh::LeanObject,
    mut v___y_4843_: *mut crate::leanh::LeanObject,
    mut v___y_4844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4846_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___redArg(v___x_4832_, v_recFVars_4833_, v___x_4834_, v___x_4835_, v_declName_4836_, v_as_x27_4838_, v_b_4839_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
    return v___x_4846_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5___boxed(
    mut v___x_4847_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4848_: *mut crate::leanh::LeanObject,
    mut v___x_4849_: *mut crate::leanh::LeanObject,
    mut v___x_4850_: *mut crate::leanh::LeanObject,
    mut v_declName_4851_: *mut crate::leanh::LeanObject,
    mut v_as_4852_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4853_: *mut crate::leanh::LeanObject,
    mut v_b_4854_: *mut crate::leanh::LeanObject,
    mut v_a_4855_: *mut crate::leanh::LeanObject,
    mut v___y_4856_: *mut crate::leanh::LeanObject,
    mut v___y_4857_: *mut crate::leanh::LeanObject,
    mut v___y_4858_: *mut crate::leanh::LeanObject,
    mut v___y_4859_: *mut crate::leanh::LeanObject,
    mut v___y_4860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4861_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__5(v___x_4847_, v_recFVars_4848_, v___x_4849_, v___x_4850_, v_declName_4851_, v_as_4852_, v_as_x27_4853_, v_b_4854_, v_a_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
    crate::leanh::lean_dec(v___y_4859_);
    crate::leanh::lean_dec_ref(v___y_4858_);
    crate::leanh::lean_dec(v___y_4857_);
    crate::leanh::lean_dec_ref(v___y_4856_);
    crate::leanh::lean_dec(v_as_x27_4853_);
    crate::leanh::lean_dec(v_as_4852_);
    crate::leanh::lean_dec(v_declName_4851_);
    crate::leanh::lean_dec_ref(v___x_4850_);
    crate::leanh::lean_dec_ref(v_recFVars_4848_);
    crate::leanh::lean_dec(v___x_4847_);
    return v_res_4861_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6(
    mut v___x_4862_: *mut crate::leanh::LeanObject,
    mut v___x_4863_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4864_: *mut crate::leanh::LeanObject,
    mut v_a_4865_: *mut crate::leanh::LeanObject,
    mut v_declName_4866_: *mut crate::leanh::LeanObject,
    mut v_as_4867_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4868_: *mut crate::leanh::LeanObject,
    mut v_b_4869_: *mut crate::leanh::LeanObject,
    mut v_a_4870_: *mut crate::leanh::LeanObject,
    mut v___y_4871_: *mut crate::leanh::LeanObject,
    mut v___y_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
    mut v___y_4874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4876_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___redArg(v___x_4862_, v___x_4863_, v_recFVars_4864_, v_a_4865_, v_declName_4866_, v_as_x27_4868_, v_b_4869_);
    return v___x_4876_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6___boxed(
    mut v___x_4877_: *mut crate::leanh::LeanObject,
    mut v___x_4878_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4879_: *mut crate::leanh::LeanObject,
    mut v_a_4880_: *mut crate::leanh::LeanObject,
    mut v_declName_4881_: *mut crate::leanh::LeanObject,
    mut v_as_4882_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4883_: *mut crate::leanh::LeanObject,
    mut v_b_4884_: *mut crate::leanh::LeanObject,
    mut v_a_4885_: *mut crate::leanh::LeanObject,
    mut v___y_4886_: *mut crate::leanh::LeanObject,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4891_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__6(v___x_4877_, v___x_4878_, v_recFVars_4879_, v_a_4880_, v_declName_4881_, v_as_4882_, v_as_x27_4883_, v_b_4884_, v_a_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
    crate::leanh::lean_dec(v___y_4889_);
    crate::leanh::lean_dec_ref(v___y_4888_);
    crate::leanh::lean_dec(v___y_4887_);
    crate::leanh::lean_dec_ref(v___y_4886_);
    crate::leanh::lean_dec(v_as_x27_4883_);
    crate::leanh::lean_dec(v_as_4882_);
    crate::leanh::lean_dec(v_declName_4881_);
    crate::leanh::lean_dec(v_a_4880_);
    crate::leanh::lean_dec_ref(v_recFVars_4879_);
    crate::leanh::lean_dec(v___x_4878_);
    crate::leanh::lean_dec(v___x_4877_);
    return v_res_4891_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7(
    mut v___x_4892_: *mut crate::leanh::LeanObject,
    mut v___x_4893_: *mut crate::leanh::LeanObject,
    mut v___x_4894_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4895_: *mut crate::leanh::LeanObject,
    mut v_as_4896_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4897_: *mut crate::leanh::LeanObject,
    mut v_b_4898_: *mut crate::leanh::LeanObject,
    mut v_a_4899_: *mut crate::leanh::LeanObject,
    mut v___y_4900_: *mut crate::leanh::LeanObject,
    mut v___y_4901_: *mut crate::leanh::LeanObject,
    mut v___y_4902_: *mut crate::leanh::LeanObject,
    mut v___y_4903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4905_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___redArg(v___x_4892_, v___x_4893_, v___x_4894_, v_recFVars_4895_, v_as_x27_4897_, v_b_4898_);
    return v___x_4905_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7___boxed(
    mut v___x_4906_: *mut crate::leanh::LeanObject,
    mut v___x_4907_: *mut crate::leanh::LeanObject,
    mut v___x_4908_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4909_: *mut crate::leanh::LeanObject,
    mut v_as_4910_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4911_: *mut crate::leanh::LeanObject,
    mut v_b_4912_: *mut crate::leanh::LeanObject,
    mut v_a_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
    mut v___y_4915_: *mut crate::leanh::LeanObject,
    mut v___y_4916_: *mut crate::leanh::LeanObject,
    mut v___y_4917_: *mut crate::leanh::LeanObject,
    mut v___y_4918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4919_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__7(v___x_4906_, v___x_4907_, v___x_4908_, v_recFVars_4909_, v_as_4910_, v_as_x27_4911_, v_b_4912_, v_a_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_);
    crate::leanh::lean_dec(v___y_4917_);
    crate::leanh::lean_dec_ref(v___y_4916_);
    crate::leanh::lean_dec(v___y_4915_);
    crate::leanh::lean_dec_ref(v___y_4914_);
    crate::leanh::lean_dec(v_as_x27_4911_);
    crate::leanh::lean_dec(v_as_4910_);
    crate::leanh::lean_dec_ref(v_recFVars_4909_);
    crate::leanh::lean_dec(v___x_4908_);
    crate::leanh::lean_dec(v___x_4907_);
    crate::leanh::lean_dec(v___x_4906_);
    return v_res_4919_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10(
    mut v___x_4920_: *mut crate::leanh::LeanObject,
    mut v___x_4921_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4922_: *mut crate::leanh::LeanObject,
    mut v_as_4923_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4924_: *mut crate::leanh::LeanObject,
    mut v_b_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
    mut v___y_4927_: *mut crate::leanh::LeanObject,
    mut v___y_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4932_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___redArg(v___x_4920_, v___x_4921_, v_recFVars_4922_, v_as_x27_4924_, v_b_4925_);
    return v___x_4932_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10___boxed(
    mut v___x_4933_: *mut crate::leanh::LeanObject,
    mut v___x_4934_: *mut crate::leanh::LeanObject,
    mut v_recFVars_4935_: *mut crate::leanh::LeanObject,
    mut v_as_4936_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4937_: *mut crate::leanh::LeanObject,
    mut v_b_4938_: *mut crate::leanh::LeanObject,
    mut v_a_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
    mut v___y_4943_: *mut crate::leanh::LeanObject,
    mut v___y_4944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4945_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__10(v___x_4933_, v___x_4934_, v_recFVars_4935_, v_as_4936_, v_as_x27_4937_, v_b_4938_, v_a_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
    crate::leanh::lean_dec(v___y_4943_);
    crate::leanh::lean_dec_ref(v___y_4942_);
    crate::leanh::lean_dec(v___y_4941_);
    crate::leanh::lean_dec_ref(v___y_4940_);
    crate::leanh::lean_dec(v_as_x27_4937_);
    crate::leanh::lean_dec(v_as_4936_);
    crate::leanh::lean_dec_ref(v_recFVars_4935_);
    crate::leanh::lean_dec(v___x_4934_);
    crate::leanh::lean_dec(v___x_4933_);
    return v_res_4945_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11(
    mut v_00_u03b1_4946_: *mut crate::leanh::LeanObject,
    mut v_msg_4947_: *mut crate::leanh::LeanObject,
    mut v___y_4948_: *mut crate::leanh::LeanObject,
    mut v___y_4949_: *mut crate::leanh::LeanObject,
    mut v___y_4950_: *mut crate::leanh::LeanObject,
    mut v___y_4951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4953_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___redArg(v_msg_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
    return v___x_4953_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11___boxed(
    mut v_00_u03b1_4954_: *mut crate::leanh::LeanObject,
    mut v_msg_4955_: *mut crate::leanh::LeanObject,
    mut v___y_4956_: *mut crate::leanh::LeanObject,
    mut v___y_4957_: *mut crate::leanh::LeanObject,
    mut v___y_4958_: *mut crate::leanh::LeanObject,
    mut v___y_4959_: *mut crate::leanh::LeanObject,
    mut v___y_4960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4961_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11(v_00_u03b1_4954_, v_msg_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
    crate::leanh::lean_dec(v___y_4959_);
    crate::leanh::lean_dec_ref(v___y_4958_);
    crate::leanh::lean_dec(v___y_4957_);
    crate::leanh::lean_dec_ref(v___y_4956_);
    return v_res_4961_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3(
    mut v_00_u03b1_4962_: *mut crate::leanh::LeanObject,
    mut v_constName_4963_: *mut crate::leanh::LeanObject,
    mut v___y_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
    mut v___y_4966_: *mut crate::leanh::LeanObject,
    mut v___y_4967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4969_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___redArg(v_constName_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
    return v___x_4969_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3___boxed(
    mut v_00_u03b1_4970_: *mut crate::leanh::LeanObject,
    mut v_constName_4971_: *mut crate::leanh::LeanObject,
    mut v___y_4972_: *mut crate::leanh::LeanObject,
    mut v___y_4973_: *mut crate::leanh::LeanObject,
    mut v___y_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4977_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3(v_00_u03b1_4970_, v_constName_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
    crate::leanh::lean_dec(v___y_4975_);
    crate::leanh::lean_dec_ref(v___y_4974_);
    crate::leanh::lean_dec(v___y_4973_);
    crate::leanh::lean_dec_ref(v___y_4972_);
    return v_res_4977_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6(
    mut v_00_u03b1_4978_: *mut crate::leanh::LeanObject,
    mut v_ref_4979_: *mut crate::leanh::LeanObject,
    mut v_constName_4980_: *mut crate::leanh::LeanObject,
    mut v___y_4981_: *mut crate::leanh::LeanObject,
    mut v___y_4982_: *mut crate::leanh::LeanObject,
    mut v___y_4983_: *mut crate::leanh::LeanObject,
    mut v___y_4984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___redArg(v_ref_4979_, v_constName_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_);
    return v___x_4986_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b1_4987_: *mut crate::leanh::LeanObject,
    mut v_ref_4988_: *mut crate::leanh::LeanObject,
    mut v_constName_4989_: *mut crate::leanh::LeanObject,
    mut v___y_4990_: *mut crate::leanh::LeanObject,
    mut v___y_4991_: *mut crate::leanh::LeanObject,
    mut v___y_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4995_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6(v_00_u03b1_4987_, v_ref_4988_, v_constName_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
    crate::leanh::lean_dec(v___y_4993_);
    crate::leanh::lean_dec_ref(v___y_4992_);
    crate::leanh::lean_dec(v___y_4991_);
    crate::leanh::lean_dec_ref(v___y_4990_);
    crate::leanh::lean_dec(v_ref_4988_);
    return v_res_4995_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16(
    mut v_00_u03b1_4996_: *mut crate::leanh::LeanObject,
    mut v_ref_4997_: *mut crate::leanh::LeanObject,
    mut v_msg_4998_: *mut crate::leanh::LeanObject,
    mut v_declHint_4999_: *mut crate::leanh::LeanObject,
    mut v___y_5000_: *mut crate::leanh::LeanObject,
    mut v___y_5001_: *mut crate::leanh::LeanObject,
    mut v___y_5002_: *mut crate::leanh::LeanObject,
    mut v___y_5003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5005_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___redArg(v_ref_4997_, v_msg_4998_, v_declHint_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
    return v___x_5005_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16___boxed(
    mut v_00_u03b1_5006_: *mut crate::leanh::LeanObject,
    mut v_ref_5007_: *mut crate::leanh::LeanObject,
    mut v_msg_5008_: *mut crate::leanh::LeanObject,
    mut v_declHint_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v___y_5011_: *mut crate::leanh::LeanObject,
    mut v___y_5012_: *mut crate::leanh::LeanObject,
    mut v___y_5013_: *mut crate::leanh::LeanObject,
    mut v___y_5014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5015_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16(v_00_u03b1_5006_, v_ref_5007_, v_msg_5008_, v_declHint_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
    crate::leanh::lean_dec(v___y_5013_);
    crate::leanh::lean_dec_ref(v___y_5012_);
    crate::leanh::lean_dec(v___y_5011_);
    crate::leanh::lean_dec_ref(v___y_5010_);
    crate::leanh::lean_dec(v_ref_5007_);
    return v_res_5015_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18(
    mut v_msg_5016_: *mut crate::leanh::LeanObject,
    mut v_declHint_5017_: *mut crate::leanh::LeanObject,
    mut v___y_5018_: *mut crate::leanh::LeanObject,
    mut v___y_5019_: *mut crate::leanh::LeanObject,
    mut v___y_5020_: *mut crate::leanh::LeanObject,
    mut v___y_5021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___redArg(v_msg_5016_, v_declHint_5017_, v___y_5021_);
    return v___x_5023_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18___boxed(
    mut v_msg_5024_: *mut crate::leanh::LeanObject,
    mut v_declHint_5025_: *mut crate::leanh::LeanObject,
    mut v___y_5026_: *mut crate::leanh::LeanObject,
    mut v___y_5027_: *mut crate::leanh::LeanObject,
    mut v___y_5028_: *mut crate::leanh::LeanObject,
    mut v___y_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5031_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__17_spec__18(v_msg_5024_, v_declHint_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
    crate::leanh::lean_dec(v___y_5029_);
    crate::leanh::lean_dec_ref(v___y_5028_);
    crate::leanh::lean_dec(v___y_5027_);
    crate::leanh::lean_dec_ref(v___y_5026_);
    return v_res_5031_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18(
    mut v_00_u03b1_5032_: *mut crate::leanh::LeanObject,
    mut v_ref_5033_: *mut crate::leanh::LeanObject,
    mut v_msg_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5040_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___redArg(v_ref_5033_, v_msg_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
    return v___x_5040_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18___boxed(
    mut v_00_u03b1_5041_: *mut crate::leanh::LeanObject,
    mut v_ref_5042_: *mut crate::leanh::LeanObject,
    mut v_msg_5043_: *mut crate::leanh::LeanObject,
    mut v___y_5044_: *mut crate::leanh::LeanObject,
    mut v___y_5045_: *mut crate::leanh::LeanObject,
    mut v___y_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5049_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__2_spec__3_spec__6_spec__16_spec__18(v_00_u03b1_5041_, v_ref_5042_, v_msg_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
    crate::leanh::lean_dec(v___y_5047_);
    crate::leanh::lean_dec_ref(v___y_5046_);
    crate::leanh::lean_dec(v___y_5045_);
    crate::leanh::lean_dec_ref(v___y_5044_);
    crate::leanh::lean_dec(v_ref_5042_);
    return v_res_5049_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5050_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5051_ = lean_mk_empty_array_with_capacity(v___x_5050_);
    v___x_5052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5052_, 0, v___x_5051_);
    return v___x_5052_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5053_: usize = 0;
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5053_ = 5usize;
    v___x_5054_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5055_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5056_ = lean_mk_empty_array_with_capacity(v___x_5055_);
    v___x_5057_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__0);
    v___x_5058_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5058_, 0, v___x_5057_);
    crate::leanh::lean_ctor_set(v___x_5058_, 1, v___x_5056_);
    crate::leanh::lean_ctor_set(v___x_5058_, 2, v___x_5054_);
    crate::leanh::lean_ctor_set(v___x_5058_, 3, v___x_5054_);
    crate::leanh::lean_ctor_set_usize(v___x_5058_, 4, v___x_5053_);
    return v___x_5058_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg(
    mut v___y_5059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5076_: u8 = 0;
    let mut v_tid_5077_: u64 = 0;
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5080_: u8 = 0;
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_unused_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5061_ = lean_st_ref_get(v___y_5059_);
                v_traceState_5062_ = crate::leanh::lean_ctor_get(v___x_5061_, 4);
                crate::leanh::lean_inc_ref(v_traceState_5062_);
                crate::leanh::lean_dec(v___x_5061_);
                v_traces_5063_ = crate::leanh::lean_ctor_get(v_traceState_5062_, 0);
                crate::leanh::lean_inc_ref(v_traces_5063_);
                crate::leanh::lean_dec_ref(v_traceState_5062_);
                v___x_5064_ = lean_st_ref_take(v___y_5059_);
                v_traceState_5065_ = crate::leanh::lean_ctor_get(v___x_5064_, 4);
                v_env_5066_ = crate::leanh::lean_ctor_get(v___x_5064_, 0);
                v_nextMacroScope_5067_ = crate::leanh::lean_ctor_get(v___x_5064_, 1);
                v_ngen_5068_ = crate::leanh::lean_ctor_get(v___x_5064_, 2);
                v_auxDeclNGen_5069_ = crate::leanh::lean_ctor_get(v___x_5064_, 3);
                v_cache_5070_ = crate::leanh::lean_ctor_get(v___x_5064_, 5);
                v_messages_5071_ = crate::leanh::lean_ctor_get(v___x_5064_, 6);
                v_infoState_5072_ = crate::leanh::lean_ctor_get(v___x_5064_, 7);
                v_snapshotTasks_5073_ = crate::leanh::lean_ctor_get(v___x_5064_, 8);
                v_isSharedCheck_5092_ = (!crate::leanh::lean_is_exclusive(v___x_5064_)) as u8;
                if v_isSharedCheck_5092_ == 0 {
                    v___x_5075_ = v___x_5064_;
                    v_isShared_5076_ = v_isSharedCheck_5092_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5073_);
                    crate::leanh::lean_inc(v_infoState_5072_);
                    crate::leanh::lean_inc(v_messages_5071_);
                    crate::leanh::lean_inc(v_cache_5070_);
                    crate::leanh::lean_inc(v_traceState_5065_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5069_);
                    crate::leanh::lean_inc(v_ngen_5068_);
                    crate::leanh::lean_inc(v_nextMacroScope_5067_);
                    crate::leanh::lean_inc(v_env_5066_);
                    crate::leanh::lean_dec(v___x_5064_);
                    v___x_5075_ = crate::leanh::lean_box(0);
                    v_isShared_5076_ = v_isSharedCheck_5092_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_5077_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5065_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5090_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5065_)) as u8;
                if v_isSharedCheck_5090_ == 0 {
                    v_unused_5091_ = crate::leanh::lean_ctor_get(v_traceState_5065_, 0);
                    crate::leanh::lean_dec(v_unused_5091_);
                    v___x_5079_ = v_traceState_5065_;
                    v_isShared_5080_ = v_isSharedCheck_5090_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_5065_);
                    v___x_5079_ = crate::leanh::lean_box(0);
                    v_isShared_5080_ = v_isSharedCheck_5090_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5081_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___closed__1);
                if v_isShared_5080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5079_, 0, v___x_5081_);
                    v___x_5083_ = v___x_5079_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5081_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5089_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5077_,
                    );
                    v___x_5083_ = v_reuseFailAlloc_5089_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5076_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5075_, 4, v___x_5083_);
                    v___x_5085_ = v___x_5075_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5088_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_env_5066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 1, v_nextMacroScope_5067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 2, v_ngen_5068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 3, v_auxDeclNGen_5069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 4, v___x_5083_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 5, v_cache_5070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 6, v_messages_5071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 7, v_infoState_5072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 8, v_snapshotTasks_5073_);
                    v___x_5085_ = v_reuseFailAlloc_5088_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5086_ = lean_st_ref_set(v___y_5059_, v___x_5085_);
                v___x_5087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5087_, 0, v_traces_5063_);
                return v___x_5087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg___boxed(
    mut v___y_5093_: *mut crate::leanh::LeanObject,
    mut v___y_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5095_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg(
            v___y_5093_,
        );
    crate::leanh::lean_dec(v___y_5093_);
    return v_res_5095_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1(
    mut v___y_5096_: *mut crate::leanh::LeanObject,
    mut v___y_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5101_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg(
            v___y_5099_,
        );
    return v___x_5101_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___boxed(
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5107_ =
        l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1(
            v___y_5102_,
            v___y_5103_,
            v___y_5104_,
            v___y_5105_,
        );
    crate::leanh::lean_dec(v___y_5105_);
    crate::leanh::lean_dec_ref(v___y_5104_);
    crate::leanh::lean_dec(v___y_5103_);
    crate::leanh::lean_dec_ref(v___y_5102_);
    return v_res_5107_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2(
    mut v_opts_5108_: *mut crate::leanh::LeanObject,
    mut v_opt_5109_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5110_ = crate::leanh::lean_ctor_get(v_opt_5109_, 0);
    v_defValue_5111_ = crate::leanh::lean_ctor_get(v_opt_5109_, 1);
    v_map_5112_ = crate::leanh::lean_ctor_get(v_opts_5108_, 0);
    v___x_5113_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5112_,
            v_name_5110_,
        );
    if crate::leanh::lean_obj_tag(v___x_5113_) == 0 {
        let mut v___x_5114_: u8 = 0;
        v___x_5114_ = (crate::leanh::lean_unbox(v_defValue_5111_) as u8);
        return v___x_5114_;
    } else {
        let mut v_val_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5115_ = crate::leanh::lean_ctor_get(v___x_5113_, 0);
        crate::leanh::lean_inc(v_val_5115_);
        crate::leanh::lean_dec_ref_known(v___x_5113_, 1);
        if crate::leanh::lean_obj_tag(v_val_5115_) == 1 {
            let mut v_v_5116_: u8 = 0;
            v_v_5116_ = crate::leanh::lean_ctor_get_uint8(v_val_5115_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5115_, 0);
            return v_v_5116_;
        } else {
            let mut v___x_5117_: u8 = 0;
            crate::leanh::lean_dec(v_val_5115_);
            v___x_5117_ = (crate::leanh::lean_unbox(v_defValue_5111_) as u8);
            return v___x_5117_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2___boxed(
    mut v_opts_5118_: *mut crate::leanh::LeanObject,
    mut v_opt_5119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5120_: u8 = 0;
    let mut v_r_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5120_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2(v_opts_5118_, v_opt_5119_);
    crate::leanh::lean_dec_ref(v_opt_5119_);
    crate::leanh::lean_dec_ref(v_opts_5118_);
    v_r_5121_ = crate::leanh::lean_box((v_res_5120_) as usize);
    return v_r_5121_;
}
pub unsafe fn l_Lean_mkCasesOn___lam__0(
    mut v_declName_5122_: *mut crate::leanh::LeanObject,
    mut v_x_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5129_ = l_Lean_MessageData_ofName(v_declName_5122_);
    v___x_5130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5130_, 0, v___x_5129_);
    return v___x_5130_;
}
pub unsafe fn l_Lean_mkCasesOn___lam__0___boxed(
    mut v_declName_5131_: *mut crate::leanh::LeanObject,
    mut v_x_5132_: *mut crate::leanh::LeanObject,
    mut v___y_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5138_ = l_Lean_mkCasesOn___lam__0(
        v_declName_5131_,
        v_x_5132_,
        v___y_5133_,
        v___y_5134_,
        v___y_5135_,
        v___y_5136_,
    );
    crate::leanh::lean_dec(v___y_5136_);
    crate::leanh::lean_dec_ref(v___y_5135_);
    crate::leanh::lean_dec(v___y_5134_);
    crate::leanh::lean_dec_ref(v___y_5133_);
    crate::leanh::lean_dec_ref(v_x_5132_);
    return v_res_5138_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__7(
    mut v_opts_5139_: *mut crate::leanh::LeanObject,
    mut v_opt_5140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5141_ = crate::leanh::lean_ctor_get(v_opt_5140_, 0);
    v_defValue_5142_ = crate::leanh::lean_ctor_get(v_opt_5140_, 1);
    v_map_5143_ = crate::leanh::lean_ctor_get(v_opts_5139_, 0);
    v___x_5144_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5143_,
            v_name_5141_,
        );
    if crate::leanh::lean_obj_tag(v___x_5144_) == 0 {
        crate::leanh::lean_inc(v_defValue_5142_);
        return v_defValue_5142_;
    } else {
        let mut v_val_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5145_ = crate::leanh::lean_ctor_get(v___x_5144_, 0);
        crate::leanh::lean_inc(v_val_5145_);
        crate::leanh::lean_dec_ref_known(v___x_5144_, 1);
        if crate::leanh::lean_obj_tag(v_val_5145_) == 3 {
            let mut v_v_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_5146_ = crate::leanh::lean_ctor_get(v_val_5145_, 0);
            crate::leanh::lean_inc(v_v_5146_);
            crate::leanh::lean_dec_ref_known(v_val_5145_, 1);
            return v_v_5146_;
        } else {
            crate::leanh::lean_dec(v_val_5145_);
            crate::leanh::lean_inc(v_defValue_5142_);
            return v_defValue_5142_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__7___boxed(
    mut v_opts_5147_: *mut crate::leanh::LeanObject,
    mut v_opt_5148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5149_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__7(v_opts_5147_, v_opt_5148_);
    crate::leanh::lean_dec_ref(v_opt_5148_);
    crate::leanh::lean_dec_ref(v_opts_5147_);
    return v_res_5149_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(
    mut v_x_5150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5155_: u8 = 0;
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5159_: u8 = 0;
    let mut v_a_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5163_: u8 = 0;
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5150_) == 0 {
                    v_a_5152_ = crate::leanh::lean_ctor_get(v_x_5150_, 0);
                    v_isSharedCheck_5159_ = (!crate::leanh::lean_is_exclusive(v_x_5150_)) as u8;
                    if v_isSharedCheck_5159_ == 0 {
                        v___x_5154_ = v_x_5150_;
                        v_isShared_5155_ = v_isSharedCheck_5159_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5152_);
                        crate::leanh::lean_dec(v_x_5150_);
                        v___x_5154_ = crate::leanh::lean_box(0);
                        v_isShared_5155_ = v_isSharedCheck_5159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5160_ = crate::leanh::lean_ctor_get(v_x_5150_, 0);
                    v_isSharedCheck_5167_ = (!crate::leanh::lean_is_exclusive(v_x_5150_)) as u8;
                    if v_isSharedCheck_5167_ == 0 {
                        v___x_5162_ = v_x_5150_;
                        v_isShared_5163_ = v_isSharedCheck_5167_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5160_);
                        crate::leanh::lean_dec(v_x_5150_);
                        v___x_5162_ = crate::leanh::lean_box(0);
                        v_isShared_5163_ = v_isSharedCheck_5167_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5155_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5154_, 1);
                    v___x_5157_ = v___x_5154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_a_5152_);
                    v___x_5157_ = v_reuseFailAlloc_5158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5157_;
            }
            3 => {
                if v_isShared_5163_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5162_, 0);
                    v___x_5165_ = v___x_5162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_a_5160_);
                    v___x_5165_ = v_reuseFailAlloc_5166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg___boxed(
    mut v_x_5168_: *mut crate::leanh::LeanObject,
    mut v___y_5169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5170_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(v_x_5168_);
    return v_res_5170_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__4(
    mut v_e_5171_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_5171_) == 0 {
        let mut v___x_5172_: u8 = 0;
        v___x_5172_ = 2;
        return v___x_5172_;
    } else {
        let mut v___x_5173_: u8 = 0;
        v___x_5173_ = 0;
        return v___x_5173_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__4___boxed(
    mut v_e_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5175_: u8 = 0;
    let mut v_r_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__4(v_e_5174_);
    crate::leanh::lean_dec_ref(v_e_5174_);
    v_r_5176_ = crate::leanh::lean_box((v_res_5175_) as usize);
    return v_r_5176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5_spec__6(
    mut v_sz_5177_: usize,
    mut v_i_5178_: usize,
    mut v_bs_5179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5180_: u8 = 0;
    let mut v_v_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: usize = 0;
    let mut v___x_5186_: usize = 0;
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5180_ = lean_usize_dec_lt(v_i_5178_, v_sz_5177_);
                if v___x_5180_ == 0 {
                    return v_bs_5179_;
                } else {
                    v_v_5181_ = lean_array_uget_borrowed(v_bs_5179_, v_i_5178_);
                    v_msg_5182_ = crate::leanh::lean_ctor_get(v_v_5181_, 1);
                    crate::leanh::lean_inc_ref(v_msg_5182_);
                    v___x_5183_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5184_ = lean_array_uset(v_bs_5179_, v_i_5178_, v___x_5183_);
                    v___x_5185_ = 1usize;
                    v___x_5186_ = lean_usize_add(v_i_5178_, v___x_5185_);
                    v___x_5187_ = lean_array_uset(v_bs_x27_5184_, v_i_5178_, v_msg_5182_);
                    v_i_5178_ = v___x_5186_;
                    v_bs_5179_ = v___x_5187_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5_spec__6___boxed(
    mut v_sz_5189_: *mut crate::leanh::LeanObject,
    mut v_i_5190_: *mut crate::leanh::LeanObject,
    mut v_bs_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5192_: usize = 0;
    let mut v_i_boxed_5193_: usize = 0;
    let mut v_res_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5192_ = crate::leanh::lean_unbox_usize(v_sz_5189_);
    crate::leanh::lean_dec(v_sz_5189_);
    v_i_boxed_5193_ = crate::leanh::lean_unbox_usize(v_i_5190_);
    crate::leanh::lean_dec(v_i_5190_);
    v_res_5194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5_spec__6(v_sz_boxed_5192_, v_i_boxed_5193_, v_bs_5191_);
    return v_res_5194_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5(
    mut v_oldTraces_5195_: *mut crate::leanh::LeanObject,
    mut v_data_5196_: *mut crate::leanh::LeanObject,
    mut v_ref_5197_: *mut crate::leanh::LeanObject,
    mut v_msg_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
    mut v___y_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5216_: u8 = 0;
    let mut v_cancelTk_x3f_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5218_: u8 = 0;
    let mut v_inheritedTraceOptions_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5226_: usize = 0;
    let mut v___x_5227_: usize = 0;
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5234_: u8 = 0;
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5247_: u8 = 0;
    let mut v_tid_5248_: u64 = 0;
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5265_: u8 = 0;
    let mut v_unused_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5204_ = crate::leanh::lean_ctor_get(v___y_5201_, 0);
                v_fileMap_5205_ = crate::leanh::lean_ctor_get(v___y_5201_, 1);
                v_options_5206_ = crate::leanh::lean_ctor_get(v___y_5201_, 2);
                v_currRecDepth_5207_ = crate::leanh::lean_ctor_get(v___y_5201_, 3);
                v_maxRecDepth_5208_ = crate::leanh::lean_ctor_get(v___y_5201_, 4);
                v_ref_5209_ = crate::leanh::lean_ctor_get(v___y_5201_, 5);
                v_currNamespace_5210_ = crate::leanh::lean_ctor_get(v___y_5201_, 6);
                v_openDecls_5211_ = crate::leanh::lean_ctor_get(v___y_5201_, 7);
                v_initHeartbeats_5212_ = crate::leanh::lean_ctor_get(v___y_5201_, 8);
                v_maxHeartbeats_5213_ = crate::leanh::lean_ctor_get(v___y_5201_, 9);
                v_quotContext_5214_ = crate::leanh::lean_ctor_get(v___y_5201_, 10);
                v_currMacroScope_5215_ = crate::leanh::lean_ctor_get(v___y_5201_, 11);
                v_diag_5216_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5201_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5217_ = crate::leanh::lean_ctor_get(v___y_5201_, 12);
                v_suppressElabErrors_5218_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5201_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5219_ = crate::leanh::lean_ctor_get(v___y_5201_, 13);
                v___x_5220_ = lean_st_ref_get(v___y_5202_);
                v_traceState_5221_ = crate::leanh::lean_ctor_get(v___x_5220_, 4);
                crate::leanh::lean_inc_ref(v_traceState_5221_);
                crate::leanh::lean_dec(v___x_5220_);
                v_traces_5222_ = crate::leanh::lean_ctor_get(v_traceState_5221_, 0);
                crate::leanh::lean_inc_ref(v_traces_5222_);
                crate::leanh::lean_dec_ref(v_traceState_5221_);
                v_ref_5223_ = l_Lean_replaceRef(v_ref_5197_, v_ref_5209_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5219_);
                crate::leanh::lean_inc(v_cancelTk_x3f_5217_);
                crate::leanh::lean_inc(v_currMacroScope_5215_);
                crate::leanh::lean_inc(v_quotContext_5214_);
                crate::leanh::lean_inc(v_maxHeartbeats_5213_);
                crate::leanh::lean_inc(v_initHeartbeats_5212_);
                crate::leanh::lean_inc(v_openDecls_5211_);
                crate::leanh::lean_inc(v_currNamespace_5210_);
                crate::leanh::lean_inc(v_maxRecDepth_5208_);
                crate::leanh::lean_inc(v_currRecDepth_5207_);
                crate::leanh::lean_inc_ref(v_options_5206_);
                crate::leanh::lean_inc_ref(v_fileMap_5205_);
                crate::leanh::lean_inc_ref(v_fileName_5204_);
                v___x_5224_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_5224_, 0, v_fileName_5204_);
                crate::leanh::lean_ctor_set(v___x_5224_, 1, v_fileMap_5205_);
                crate::leanh::lean_ctor_set(v___x_5224_, 2, v_options_5206_);
                crate::leanh::lean_ctor_set(v___x_5224_, 3, v_currRecDepth_5207_);
                crate::leanh::lean_ctor_set(v___x_5224_, 4, v_maxRecDepth_5208_);
                crate::leanh::lean_ctor_set(v___x_5224_, 5, v_ref_5223_);
                crate::leanh::lean_ctor_set(v___x_5224_, 6, v_currNamespace_5210_);
                crate::leanh::lean_ctor_set(v___x_5224_, 7, v_openDecls_5211_);
                crate::leanh::lean_ctor_set(v___x_5224_, 8, v_initHeartbeats_5212_);
                crate::leanh::lean_ctor_set(v___x_5224_, 9, v_maxHeartbeats_5213_);
                crate::leanh::lean_ctor_set(v___x_5224_, 10, v_quotContext_5214_);
                crate::leanh::lean_ctor_set(v___x_5224_, 11, v_currMacroScope_5215_);
                crate::leanh::lean_ctor_set(v___x_5224_, 12, v_cancelTk_x3f_5217_);
                crate::leanh::lean_ctor_set(v___x_5224_, 13, v_inheritedTraceOptions_5219_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5224_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_5216_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5224_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5218_,
                );
                v___x_5225_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5222_);
                crate::leanh::lean_dec_ref(v_traces_5222_);
                v_sz_5226_ = lean_array_size(v___x_5225_);
                v___x_5227_ = 0usize;
                v___x_5228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5_spec__6(v_sz_5226_, v___x_5227_, v___x_5225_);
                v_msg_5229_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_5229_, 0, v_data_5196_);
                crate::leanh::lean_ctor_set(v_msg_5229_, 1, v_msg_5198_);
                crate::leanh::lean_ctor_set(v_msg_5229_, 2, v___x_5228_);
                v___x_5230_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl_spec__11_spec__13(v_msg_5229_, v___y_5199_, v___y_5200_, v___x_5224_, v___y_5202_);
                crate::leanh::lean_dec_ref_known(v___x_5224_, 14);
                v_a_5231_ = crate::leanh::lean_ctor_get(v___x_5230_, 0);
                v_isSharedCheck_5268_ = (!crate::leanh::lean_is_exclusive(v___x_5230_)) as u8;
                if v_isSharedCheck_5268_ == 0 {
                    v___x_5233_ = v___x_5230_;
                    v_isShared_5234_ = v_isSharedCheck_5268_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5231_);
                    crate::leanh::lean_dec(v___x_5230_);
                    v___x_5233_ = crate::leanh::lean_box(0);
                    v_isShared_5234_ = v_isSharedCheck_5268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5235_ = lean_st_ref_take(v___y_5202_);
                v_traceState_5236_ = crate::leanh::lean_ctor_get(v___x_5235_, 4);
                v_env_5237_ = crate::leanh::lean_ctor_get(v___x_5235_, 0);
                v_nextMacroScope_5238_ = crate::leanh::lean_ctor_get(v___x_5235_, 1);
                v_ngen_5239_ = crate::leanh::lean_ctor_get(v___x_5235_, 2);
                v_auxDeclNGen_5240_ = crate::leanh::lean_ctor_get(v___x_5235_, 3);
                v_cache_5241_ = crate::leanh::lean_ctor_get(v___x_5235_, 5);
                v_messages_5242_ = crate::leanh::lean_ctor_get(v___x_5235_, 6);
                v_infoState_5243_ = crate::leanh::lean_ctor_get(v___x_5235_, 7);
                v_snapshotTasks_5244_ = crate::leanh::lean_ctor_get(v___x_5235_, 8);
                v_isSharedCheck_5267_ = (!crate::leanh::lean_is_exclusive(v___x_5235_)) as u8;
                if v_isSharedCheck_5267_ == 0 {
                    v___x_5246_ = v___x_5235_;
                    v_isShared_5247_ = v_isSharedCheck_5267_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5244_);
                    crate::leanh::lean_inc(v_infoState_5243_);
                    crate::leanh::lean_inc(v_messages_5242_);
                    crate::leanh::lean_inc(v_cache_5241_);
                    crate::leanh::lean_inc(v_traceState_5236_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5240_);
                    crate::leanh::lean_inc(v_ngen_5239_);
                    crate::leanh::lean_inc(v_nextMacroScope_5238_);
                    crate::leanh::lean_inc(v_env_5237_);
                    crate::leanh::lean_dec(v___x_5235_);
                    v___x_5246_ = crate::leanh::lean_box(0);
                    v_isShared_5247_ = v_isSharedCheck_5267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5248_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5236_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_5265_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5236_)) as u8;
                if v_isSharedCheck_5265_ == 0 {
                    v_unused_5266_ = crate::leanh::lean_ctor_get(v_traceState_5236_, 0);
                    crate::leanh::lean_dec(v_unused_5266_);
                    v___x_5250_ = v_traceState_5236_;
                    v_isShared_5251_ = v_isSharedCheck_5265_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_5236_);
                    v___x_5250_ = crate::leanh::lean_box(0);
                    v_isShared_5251_ = v_isSharedCheck_5265_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5252_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5252_, 0, v_ref_5197_);
                crate::leanh::lean_ctor_set(v___x_5252_, 1, v_a_5231_);
                v___x_5253_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5195_, v___x_5252_);
                if v_isShared_5251_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5250_, 0, v___x_5253_);
                    v___x_5255_ = v___x_5250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5264_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5264_, 0, v___x_5253_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5264_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5248_,
                    );
                    v___x_5255_ = v_reuseFailAlloc_5264_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5247_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5246_, 4, v___x_5255_);
                    v___x_5257_ = v___x_5246_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_env_5237_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 1, v_nextMacroScope_5238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 2, v_ngen_5239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 3, v_auxDeclNGen_5240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 4, v___x_5255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 5, v_cache_5241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 6, v_messages_5242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 7, v_infoState_5243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 8, v_snapshotTasks_5244_);
                    v___x_5257_ = v_reuseFailAlloc_5263_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5258_ = lean_st_ref_set(v___y_5202_, v___x_5257_);
                v___x_5259_ = crate::leanh::lean_box(0);
                if v_isShared_5234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5233_, 0, v___x_5259_);
                    v___x_5261_ = v___x_5233_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___x_5259_);
                    v___x_5261_ = v_reuseFailAlloc_5262_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5___boxed(
    mut v_oldTraces_5269_: *mut crate::leanh::LeanObject,
    mut v_data_5270_: *mut crate::leanh::LeanObject,
    mut v_ref_5271_: *mut crate::leanh::LeanObject,
    mut v_msg_5272_: *mut crate::leanh::LeanObject,
    mut v___y_5273_: *mut crate::leanh::LeanObject,
    mut v___y_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5278_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5(v_oldTraces_5269_, v_data_5270_, v_ref_5271_, v_msg_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
    crate::leanh::lean_dec(v___y_5276_);
    crate::leanh::lean_dec_ref(v___y_5275_);
    crate::leanh::lean_dec(v___y_5274_);
    crate::leanh::lean_dec_ref(v___y_5273_);
    return v_res_5278_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5280_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__0;
    v___x_5281_ = l_Lean_stringToMessageData(v___x_5280_);
    return v___x_5281_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2()
-> f64 {
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: f64 = 0.0;
    v___x_5282_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5283_ = lean_float_of_nat(v___x_5282_);
    return v___x_5283_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5285_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__3;
    v___x_5286_ = l_Lean_stringToMessageData(v___x_5285_);
    return v___x_5286_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5()
-> f64 {
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: f64 = 0.0;
    v___x_5287_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_5288_ = lean_float_of_nat(v___x_5287_);
    return v___x_5288_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3(
    mut v_cls_5289_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5290_: u8,
    mut v_tag_5291_: *mut crate::leanh::LeanObject,
    mut v_opts_5292_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5293_: u8,
    mut v_oldTraces_5294_: *mut crate::leanh::LeanObject,
    mut v_msg_5295_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
    mut v___y_5299_: *mut crate::leanh::LeanObject,
    mut v___y_5300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5306_: u8 = 0;
    let mut v___y_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5317_: u8 = 0;
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: u8 = 0;
    let mut v___y_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5323_: u8 = 0;
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: f64 = 0.0;
    let mut v_data_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: f64 = 0.0;
    let mut v___x_5337_: f64 = 0.0;
    let mut v_reuseFailAlloc_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5346_: u8 = 0;
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5359_: u8 = 0;
    let mut v_tid_5360_: u64 = 0;
    let mut v_traces_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut v___y_5377_: f64 = 0.0;
    let mut v___x_5378_: f64 = 0.0;
    let mut v___x_5379_: f64 = 0.0;
    let mut v___x_5380_: f64 = 0.0;
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: u8 = 0;
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: f64 = 0.0;
    let mut v___x_5387_: f64 = 0.0;
    let mut v___x_5388_: f64 = 0.0;
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: f64 = 0.0;
    let mut v_isSharedCheck_5392_: u8 = 0;
    let mut v_isSharedCheck_5393_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_5302_ = crate::leanh::lean_ctor_get(v_resStartStop_5296_, 0);
                v_snd_5303_ = crate::leanh::lean_ctor_get(v_resStartStop_5296_, 1);
                v_isSharedCheck_5393_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_5296_)) as u8;
                if v_isSharedCheck_5393_ == 0 {
                    v___x_5305_ = v_resStartStop_5296_;
                    v_isShared_5306_ = v_isSharedCheck_5393_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5303_);
                    crate::leanh::lean_inc(v_fst_5302_);
                    crate::leanh::lean_dec(v_resStartStop_5296_);
                    v___x_5305_ = crate::leanh::lean_box(0);
                    v_isShared_5306_ = v_isSharedCheck_5393_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5313_ = crate::leanh::lean_ctor_get(v_snd_5303_, 0);
                v_snd_5314_ = crate::leanh::lean_ctor_get(v_snd_5303_, 1);
                v_isSharedCheck_5392_ = (!crate::leanh::lean_is_exclusive(v_snd_5303_)) as u8;
                if v_isSharedCheck_5392_ == 0 {
                    v___x_5316_ = v_snd_5303_;
                    v_isShared_5317_ = v_isSharedCheck_5392_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5314_);
                    crate::leanh::lean_inc(v_fst_5313_);
                    crate::leanh::lean_dec(v_snd_5303_);
                    v___x_5316_ = crate::leanh::lean_box(0);
                    v_isShared_5317_ = v_isSharedCheck_5392_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_5309_);
                v___x_5311_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__5(v_oldTraces_5294_, v_data_5310_, v___y_5309_, v___y_5308_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
                if crate::leanh::lean_obj_tag(v___x_5311_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5311_, 1);
                    v___x_5312_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(v_fst_5302_);
                    return v___x_5312_;
                } else {
                    crate::leanh::lean_dec(v_fst_5302_);
                    return v___x_5311_;
                }
            }
            3 => {
                v___x_5318_ = l_Lean_trace_profiler;
                v___x_5319_ =
                    l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2(v_opts_5292_, v___x_5318_);
                if v___x_5319_ == 0 {
                    v___y_5346_ = v___x_5319_;
                    state = 8;
                    continue;
                } else {
                    v___x_5382_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_5383_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2(
                        v_opts_5292_,
                        v___x_5382_,
                    );
                    if v___x_5383_ == 0 {
                        v___x_5384_ = l_Lean_trace_profiler_threshold;
                        v___x_5385_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__7(v_opts_5292_, v___x_5384_);
                        v___x_5386_ = lean_float_of_nat(v___x_5385_);
                        v___x_5387_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__5);
                        v___x_5388_ = lean_float_div(v___x_5386_, v___x_5387_);
                        v___y_5377_ = v___x_5388_;
                        state = 13;
                        continue;
                    } else {
                        v___x_5389_ = l_Lean_trace_profiler_threshold;
                        v___x_5390_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__7(v_opts_5292_, v___x_5389_);
                        v___x_5391_ = lean_float_of_nat(v___x_5390_);
                        v___y_5377_ = v___x_5391_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_result_5323_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__4(v_fst_5302_);
                v___x_5324_ = l_Lean_TraceResult_toEmoji(v_result_5323_);
                v___x_5325_ = l_Lean_stringToMessageData(v___x_5324_);
                v___x_5326_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__1);
                if v_isShared_5317_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5316_, 7);
                    crate::leanh::lean_ctor_set(v___x_5316_, 1, v___x_5326_);
                    crate::leanh::lean_ctor_set(v___x_5316_, 0, v___x_5325_);
                    v___x_5328_ = v___x_5316_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5339_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 1, v___x_5326_);
                    v___x_5328_ = v_reuseFailAlloc_5339_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5306_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5305_, 7);
                    crate::leanh::lean_ctor_set(v___x_5305_, 1, v_a_5322_);
                    crate::leanh::lean_ctor_set(v___x_5305_, 0, v___x_5328_);
                    v_m_5330_ = v___x_5305_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5338_, 1, v_a_5322_);
                    v_m_5330_ = v_reuseFailAlloc_5338_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5331_ = crate::leanh::lean_box((v_result_5323_) as usize);
                v___x_5332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5332_, 0, v___x_5331_);
                v___x_5333_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__2);
                crate::leanh::lean_inc_ref(v_tag_5291_);
                crate::leanh::lean_inc_ref(v___x_5332_);
                crate::leanh::lean_inc(v_cls_5289_);
                v_data_5334_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_5334_, 0, v_cls_5289_);
                crate::leanh::lean_ctor_set(v_data_5334_, 1, v___x_5332_);
                crate::leanh::lean_ctor_set(v_data_5334_, 2, v_tag_5291_);
                crate::leanh::lean_ctor_set_float(
                    v_data_5334_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5333_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_5334_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5333_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_5334_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_5290_,
                );
                if v___x_5319_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5332_, 1);
                    crate::leanh::lean_dec(v_snd_5314_);
                    crate::leanh::lean_dec(v_fst_5313_);
                    crate::leanh::lean_dec_ref(v_tag_5291_);
                    crate::leanh::lean_dec(v_cls_5289_);
                    v___y_5308_ = v_m_5330_;
                    v___y_5309_ = v___y_5321_;
                    v_data_5310_ = v_data_5334_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_5334_, 3);
                    v_data_5335_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_5335_, 0, v_cls_5289_);
                    crate::leanh::lean_ctor_set(v_data_5335_, 1, v___x_5332_);
                    crate::leanh::lean_ctor_set(v_data_5335_, 2, v_tag_5291_);
                    v___x_5336_ = crate::leanh::lean_unbox_float(v_fst_5313_);
                    crate::leanh::lean_dec(v_fst_5313_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_5335_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_5336_,
                    );
                    v___x_5337_ = crate::leanh::lean_unbox_float(v_snd_5314_);
                    crate::leanh::lean_dec(v_snd_5314_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_5335_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_5337_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_5335_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_5290_,
                    );
                    v___y_5308_ = v_m_5330_;
                    v___y_5309_ = v___y_5321_;
                    v_data_5310_ = v_data_5335_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v_ref_5341_ = crate::leanh::lean_ctor_get(v___y_5299_, 5);
                crate::leanh::lean_inc(v___y_5300_);
                crate::leanh::lean_inc_ref(v___y_5299_);
                crate::leanh::lean_inc(v___y_5298_);
                crate::leanh::lean_inc_ref(v___y_5297_);
                crate::leanh::lean_inc(v_fst_5302_);
                v___x_5342_ = crate::leanh::lean_apply_6(
                    v_msg_5295_,
                    v_fst_5302_,
                    v___y_5297_,
                    v___y_5298_,
                    v___y_5299_,
                    v___y_5300_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5342_) == 0 {
                    v_a_5343_ = crate::leanh::lean_ctor_get(v___x_5342_, 0);
                    crate::leanh::lean_inc(v_a_5343_);
                    crate::leanh::lean_dec_ref_known(v___x_5342_, 1);
                    v___y_5321_ = v_ref_5341_;
                    v_a_5322_ = v_a_5343_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5342_, 1);
                    v___x_5344_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___closed__4);
                    v___y_5321_ = v_ref_5341_;
                    v_a_5322_ = v___x_5344_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                if v_clsEnabled_5293_ == 0 {
                    if v___y_5346_ == 0 {
                        crate::leanh::lean_del_object(v___x_5316_);
                        crate::leanh::lean_dec(v_snd_5314_);
                        crate::leanh::lean_dec(v_fst_5313_);
                        crate::leanh::lean_del_object(v___x_5305_);
                        crate::leanh::lean_dec_ref(v_msg_5295_);
                        crate::leanh::lean_dec_ref(v_tag_5291_);
                        crate::leanh::lean_dec(v_cls_5289_);
                        v___x_5347_ = lean_st_ref_take(v___y_5300_);
                        v_traceState_5348_ = crate::leanh::lean_ctor_get(v___x_5347_, 4);
                        v_env_5349_ = crate::leanh::lean_ctor_get(v___x_5347_, 0);
                        v_nextMacroScope_5350_ = crate::leanh::lean_ctor_get(v___x_5347_, 1);
                        v_ngen_5351_ = crate::leanh::lean_ctor_get(v___x_5347_, 2);
                        v_auxDeclNGen_5352_ = crate::leanh::lean_ctor_get(v___x_5347_, 3);
                        v_cache_5353_ = crate::leanh::lean_ctor_get(v___x_5347_, 5);
                        v_messages_5354_ = crate::leanh::lean_ctor_get(v___x_5347_, 6);
                        v_infoState_5355_ = crate::leanh::lean_ctor_get(v___x_5347_, 7);
                        v_snapshotTasks_5356_ = crate::leanh::lean_ctor_get(v___x_5347_, 8);
                        v_isSharedCheck_5375_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5347_)) as u8;
                        if v_isSharedCheck_5375_ == 0 {
                            v___x_5358_ = v___x_5347_;
                            v_isShared_5359_ = v_isSharedCheck_5375_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_5356_);
                            crate::leanh::lean_inc(v_infoState_5355_);
                            crate::leanh::lean_inc(v_messages_5354_);
                            crate::leanh::lean_inc(v_cache_5353_);
                            crate::leanh::lean_inc(v_traceState_5348_);
                            crate::leanh::lean_inc(v_auxDeclNGen_5352_);
                            crate::leanh::lean_inc(v_ngen_5351_);
                            crate::leanh::lean_inc(v_nextMacroScope_5350_);
                            crate::leanh::lean_inc(v_env_5349_);
                            crate::leanh::lean_dec(v___x_5347_);
                            v___x_5358_ = crate::leanh::lean_box(0);
                            v_isShared_5359_ = v_isSharedCheck_5375_;
                            state = 9;
                            continue;
                        }
                    } else {
                        state = 7;
                        continue;
                    }
                } else {
                    state = 7;
                    continue;
                }
            }
            9 => {
                v_tid_5360_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5348_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5361_ = crate::leanh::lean_ctor_get(v_traceState_5348_, 0);
                v_isSharedCheck_5374_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5348_)) as u8;
                if v_isSharedCheck_5374_ == 0 {
                    v___x_5363_ = v_traceState_5348_;
                    v_isShared_5364_ = v_isSharedCheck_5374_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5361_);
                    crate::leanh::lean_dec(v_traceState_5348_);
                    v___x_5363_ = crate::leanh::lean_box(0);
                    v_isShared_5364_ = v_isSharedCheck_5374_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5365_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_5294_, v_traces_5361_);
                crate::leanh::lean_dec_ref(v_traces_5361_);
                if v_isShared_5364_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5363_, 0, v___x_5365_);
                    v___x_5367_ = v___x_5363_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5373_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5365_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5373_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5360_,
                    );
                    v___x_5367_ = v_reuseFailAlloc_5373_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5359_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5358_, 4, v___x_5367_);
                    v___x_5369_ = v___x_5358_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5372_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_env_5349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 1, v_nextMacroScope_5350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 2, v_ngen_5351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 3, v_auxDeclNGen_5352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 4, v___x_5367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 5, v_cache_5353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 6, v_messages_5354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 7, v_infoState_5355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 8, v_snapshotTasks_5356_);
                    v___x_5369_ = v_reuseFailAlloc_5372_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5370_ = lean_st_ref_set(v___y_5300_, v___x_5369_);
                v___x_5371_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(v_fst_5302_);
                return v___x_5371_;
            }
            13 => {
                v___x_5378_ = crate::leanh::lean_unbox_float(v_snd_5314_);
                v___x_5379_ = crate::leanh::lean_unbox_float(v_fst_5313_);
                v___x_5380_ = lean_float_sub(v___x_5378_, v___x_5379_);
                v___x_5381_ = lean_float_decLt(v___y_5377_, v___x_5380_);
                v___y_5346_ = v___x_5381_;
                state = 8;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3___boxed(
    mut v_cls_5394_: *mut crate::leanh::LeanObject,
    mut v_collapsed_5395_: *mut crate::leanh::LeanObject,
    mut v_tag_5396_: *mut crate::leanh::LeanObject,
    mut v_opts_5397_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_5398_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_5399_: *mut crate::leanh::LeanObject,
    mut v_msg_5400_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_5401_: *mut crate::leanh::LeanObject,
    mut v___y_5402_: *mut crate::leanh::LeanObject,
    mut v___y_5403_: *mut crate::leanh::LeanObject,
    mut v___y_5404_: *mut crate::leanh::LeanObject,
    mut v___y_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_5407_: u8 = 0;
    let mut v_clsEnabled_boxed_5408_: u8 = 0;
    let mut v_res_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_5407_ = (crate::leanh::lean_unbox(v_collapsed_5395_) as u8);
    v_clsEnabled_boxed_5408_ = (crate::leanh::lean_unbox(v_clsEnabled_5398_) as u8);
    v_res_5409_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3(v_cls_5394_, v_collapsed_boxed_5407_, v_tag_5396_, v_opts_5397_, v_clsEnabled_boxed_5408_, v_oldTraces_5399_, v_msg_5400_, v_resStartStop_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
    crate::leanh::lean_dec(v___y_5405_);
    crate::leanh::lean_dec_ref(v___y_5404_);
    crate::leanh::lean_dec(v___y_5403_);
    crate::leanh::lean_dec_ref(v___y_5402_);
    crate::leanh::lean_dec_ref(v_opts_5397_);
    return v_res_5409_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5410_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5410_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5411_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0);
    v___x_5412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5412_, 0, v___x_5411_);
    return v___x_5412_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5413_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1);
    v___x_5414_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5414_, 0, v___x_5413_);
    crate::leanh::lean_ctor_set(v___x_5414_, 1, v___x_5413_);
    return v___x_5414_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5415_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1);
    v___x_5416_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5416_, 0, v___x_5415_);
    crate::leanh::lean_ctor_set(v___x_5416_, 1, v___x_5415_);
    crate::leanh::lean_ctor_set(v___x_5416_, 2, v___x_5415_);
    crate::leanh::lean_ctor_set(v___x_5416_, 3, v___x_5415_);
    crate::leanh::lean_ctor_set(v___x_5416_, 4, v___x_5415_);
    crate::leanh::lean_ctor_set(v___x_5416_, 5, v___x_5415_);
    return v___x_5416_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(
    mut v_declName_5417_: *mut crate::leanh::LeanObject,
    mut v_s_5418_: u8,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5433_: u8 = 0;
    let mut v___x_5434_: u8 = 0;
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5448_: u8 = 0;
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5456_: u8 = 0;
    let mut v_unused_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5459_: u8 = 0;
    let mut v_unused_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5422_ = lean_st_ref_take(v___y_5420_);
                v_env_5423_ = crate::leanh::lean_ctor_get(v___x_5422_, 0);
                v_nextMacroScope_5424_ = crate::leanh::lean_ctor_get(v___x_5422_, 1);
                v_ngen_5425_ = crate::leanh::lean_ctor_get(v___x_5422_, 2);
                v_auxDeclNGen_5426_ = crate::leanh::lean_ctor_get(v___x_5422_, 3);
                v_traceState_5427_ = crate::leanh::lean_ctor_get(v___x_5422_, 4);
                v_messages_5428_ = crate::leanh::lean_ctor_get(v___x_5422_, 6);
                v_infoState_5429_ = crate::leanh::lean_ctor_get(v___x_5422_, 7);
                v_snapshotTasks_5430_ = crate::leanh::lean_ctor_get(v___x_5422_, 8);
                v_isSharedCheck_5459_ = (!crate::leanh::lean_is_exclusive(v___x_5422_)) as u8;
                if v_isSharedCheck_5459_ == 0 {
                    v_unused_5460_ = crate::leanh::lean_ctor_get(v___x_5422_, 5);
                    crate::leanh::lean_dec(v_unused_5460_);
                    v___x_5432_ = v___x_5422_;
                    v_isShared_5433_ = v_isSharedCheck_5459_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5430_);
                    crate::leanh::lean_inc(v_infoState_5429_);
                    crate::leanh::lean_inc(v_messages_5428_);
                    crate::leanh::lean_inc(v_traceState_5427_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5426_);
                    crate::leanh::lean_inc(v_ngen_5425_);
                    crate::leanh::lean_inc(v_nextMacroScope_5424_);
                    crate::leanh::lean_inc(v_env_5423_);
                    crate::leanh::lean_dec(v___x_5422_);
                    v___x_5432_ = crate::leanh::lean_box(0);
                    v_isShared_5433_ = v_isSharedCheck_5459_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5434_ = 0;
                v___x_5435_ = crate::leanh::lean_box(0);
                v___x_5436_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_5423_,
                    v_declName_5417_,
                    v_s_5418_,
                    v___x_5434_,
                    v___x_5435_,
                );
                v___x_5437_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5432_, 5, v___x_5437_);
                    crate::leanh::lean_ctor_set(v___x_5432_, 0, v___x_5436_);
                    v___x_5439_ = v___x_5432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5458_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 1, v_nextMacroScope_5424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 2, v_ngen_5425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 3, v_auxDeclNGen_5426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 4, v_traceState_5427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 5, v___x_5437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 6, v_messages_5428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 7, v_infoState_5429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 8, v_snapshotTasks_5430_);
                    v___x_5439_ = v_reuseFailAlloc_5458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5440_ = lean_st_ref_set(v___y_5420_, v___x_5439_);
                v___x_5441_ = lean_st_ref_take(v___y_5419_);
                v_mctx_5442_ = crate::leanh::lean_ctor_get(v___x_5441_, 0);
                v_zetaDeltaFVarIds_5443_ = crate::leanh::lean_ctor_get(v___x_5441_, 2);
                v_postponed_5444_ = crate::leanh::lean_ctor_get(v___x_5441_, 3);
                v_diag_5445_ = crate::leanh::lean_ctor_get(v___x_5441_, 4);
                v_isSharedCheck_5456_ = (!crate::leanh::lean_is_exclusive(v___x_5441_)) as u8;
                if v_isSharedCheck_5456_ == 0 {
                    v_unused_5457_ = crate::leanh::lean_ctor_get(v___x_5441_, 1);
                    crate::leanh::lean_dec(v_unused_5457_);
                    v___x_5447_ = v___x_5441_;
                    v_isShared_5448_ = v_isSharedCheck_5456_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5445_);
                    crate::leanh::lean_inc(v_postponed_5444_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5443_);
                    crate::leanh::lean_inc(v_mctx_5442_);
                    crate::leanh::lean_dec(v___x_5441_);
                    v___x_5447_ = crate::leanh::lean_box(0);
                    v_isShared_5448_ = v_isSharedCheck_5456_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5449_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5448_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5447_, 1, v___x_5449_);
                    v___x_5451_ = v___x_5447_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5455_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_mctx_5442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5455_, 1, v___x_5449_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5455_,
                        2,
                        v_zetaDeltaFVarIds_5443_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5455_, 3, v_postponed_5444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5455_, 4, v_diag_5445_);
                    v___x_5451_ = v_reuseFailAlloc_5455_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5452_ = lean_st_ref_set(v___y_5419_, v___x_5451_);
                v___x_5453_ = crate::leanh::lean_box(0);
                v___x_5454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5454_, 0, v___x_5453_);
                return v___x_5454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(
    mut v_declName_5461_: *mut crate::leanh::LeanObject,
    mut v_s_5462_: *mut crate::leanh::LeanObject,
    mut v___y_5463_: *mut crate::leanh::LeanObject,
    mut v___y_5464_: *mut crate::leanh::LeanObject,
    mut v___y_5465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_boxed_5466_: u8 = 0;
    let mut v_res_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_5466_ = (crate::leanh::lean_unbox(v_s_5462_) as u8);
    v_res_5467_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_5461_, v_s_boxed_5466_, v___y_5463_, v___y_5464_);
    crate::leanh::lean_dec(v___y_5464_);
    crate::leanh::lean_dec(v___y_5463_);
    return v_res_5467_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
    mut v_declName_5468_: *mut crate::leanh::LeanObject,
    mut v___y_5469_: *mut crate::leanh::LeanObject,
    mut v___y_5470_: *mut crate::leanh::LeanObject,
    mut v___y_5471_: *mut crate::leanh::LeanObject,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5474_: u8 = 0;
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5474_ = 0;
    v___x_5475_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_5468_, v___x_5474_, v___y_5470_, v___y_5472_);
    return v___x_5475_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0___boxed(
    mut v_declName_5476_: *mut crate::leanh::LeanObject,
    mut v___y_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
    mut v___y_5481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5482_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
        v_declName_5476_,
        v___y_5477_,
        v___y_5478_,
        v___y_5479_,
        v___y_5480_,
    );
    crate::leanh::lean_dec(v___y_5480_);
    crate::leanh::lean_dec_ref(v___y_5479_);
    crate::leanh::lean_dec(v___y_5478_);
    crate::leanh::lean_dec_ref(v___y_5477_);
    return v_res_5482_;
}
pub unsafe fn _init_l_Lean_mkCasesOn___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5492_ = l_Lean_mkCasesOn___closed__2;
    v___x_5493_ = l_Lean_mkCasesOn___closed__5;
    v___x_5494_ = l_Lean_Name_append(v___x_5493_, v___x_5492_);
    return v___x_5494_;
}
pub unsafe fn _init_l_Lean_mkCasesOn___closed__7() -> f64 {
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: f64 = 0.0;
    v___x_5495_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_5496_ = lean_float_of_nat(v___x_5495_);
    return v___x_5496_;
}
pub unsafe fn l_Lean_mkCasesOn(
    mut v_declName_5497_: *mut crate::leanh::LeanObject,
    mut v_a_5498_: *mut crate::leanh::LeanObject,
    mut v_a_5499_: *mut crate::leanh::LeanObject,
    mut v_a_5500_: *mut crate::leanh::LeanObject,
    mut v_a_5501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5505_: u8 = 0;
    let mut v_name_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5522_: u8 = 0;
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_unused_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5545_: u8 = 0;
    let mut v_unused_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5554_: u8 = 0;
    let mut v___f_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: u8 = 0;
    let mut v___y_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: f64 = 0.0;
    let mut v___x_5566_: f64 = 0.0;
    let mut v___x_5567_: f64 = 0.0;
    let mut v___x_5568_: f64 = 0.0;
    let mut v___x_5569_: f64 = 0.0;
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5587_: u8 = 0;
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5591_: u8 = 0;
    let mut v_a_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: f64 = 0.0;
    let mut v___x_5599_: f64 = 0.0;
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5621_: u8 = 0;
    let mut v_a_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: u8 = 0;
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5644_: u8 = 0;
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5657_: u8 = 0;
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v_unused_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_unused_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: u8 = 0;
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5700_: u8 = 0;
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5707_: u8 = 0;
    let mut v_unused_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5710_: u8 = 0;
    let mut v_unused_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: u8 = 0;
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5730_: u8 = 0;
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5743_: u8 = 0;
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5750_: u8 = 0;
    let mut v_unused_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5753_: u8 = 0;
    let mut v_unused_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5758_: u8 = 0;
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5503_ = crate::leanh::lean_ctor_get(v_a_5500_, 2);
                v_inheritedTraceOptions_5504_ = crate::leanh::lean_ctor_get(v_a_5500_, 13);
                v_hasTrace_5505_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_5503_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_inc(v_declName_5497_);
                v_name_5506_ = l_Lean_mkCasesOnName(v_declName_5497_);
                if v_hasTrace_5505_ == 0 {
                    v___x_5507_ =
                        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(
                            v_declName_5497_,
                            v_a_5498_,
                            v_a_5499_,
                            v_a_5500_,
                            v_a_5501_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5507_) == 0 {
                        v_a_5508_ = crate::leanh::lean_ctor_get(v___x_5507_, 0);
                        crate::leanh::lean_inc(v_a_5508_);
                        crate::leanh::lean_dec_ref_known(v___x_5507_, 1);
                        v___x_5509_ =
                            l_Lean_addDecl(v_a_5508_, v_hasTrace_5505_, v_a_5500_, v_a_5501_);
                        if crate::leanh::lean_obj_tag(v___x_5509_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5509_, 1);
                            crate::leanh::lean_inc(v_name_5506_);
                            v___x_5510_ =
                                l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
                                    v_name_5506_,
                                    v_a_5498_,
                                    v_a_5499_,
                                    v_a_5500_,
                                    v_a_5501_,
                                );
                            crate::leanh::lean_dec_ref(v___x_5510_);
                            v___x_5511_ = lean_st_ref_take(v_a_5501_);
                            v_env_5512_ = crate::leanh::lean_ctor_get(v___x_5511_, 0);
                            v_nextMacroScope_5513_ = crate::leanh::lean_ctor_get(v___x_5511_, 1);
                            v_ngen_5514_ = crate::leanh::lean_ctor_get(v___x_5511_, 2);
                            v_auxDeclNGen_5515_ = crate::leanh::lean_ctor_get(v___x_5511_, 3);
                            v_traceState_5516_ = crate::leanh::lean_ctor_get(v___x_5511_, 4);
                            v_messages_5517_ = crate::leanh::lean_ctor_get(v___x_5511_, 6);
                            v_infoState_5518_ = crate::leanh::lean_ctor_get(v___x_5511_, 7);
                            v_snapshotTasks_5519_ = crate::leanh::lean_ctor_get(v___x_5511_, 8);
                            v_isSharedCheck_5545_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5511_)) as u8;
                            if v_isSharedCheck_5545_ == 0 {
                                v_unused_5546_ = crate::leanh::lean_ctor_get(v___x_5511_, 5);
                                crate::leanh::lean_dec(v_unused_5546_);
                                v___x_5521_ = v___x_5511_;
                                v_isShared_5522_ = v_isSharedCheck_5545_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snapshotTasks_5519_);
                                crate::leanh::lean_inc(v_infoState_5518_);
                                crate::leanh::lean_inc(v_messages_5517_);
                                crate::leanh::lean_inc(v_traceState_5516_);
                                crate::leanh::lean_inc(v_auxDeclNGen_5515_);
                                crate::leanh::lean_inc(v_ngen_5514_);
                                crate::leanh::lean_inc(v_nextMacroScope_5513_);
                                crate::leanh::lean_inc(v_env_5512_);
                                crate::leanh::lean_dec(v___x_5511_);
                                v___x_5521_ = crate::leanh::lean_box(0);
                                v_isShared_5522_ = v_isSharedCheck_5545_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_name_5506_);
                            return v___x_5509_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_5506_);
                        v_a_5547_ = crate::leanh::lean_ctor_get(v___x_5507_, 0);
                        v_isSharedCheck_5554_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5507_)) as u8;
                        if v_isSharedCheck_5554_ == 0 {
                            v___x_5549_ = v___x_5507_;
                            v_isShared_5550_ = v_isSharedCheck_5554_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5547_);
                            crate::leanh::lean_dec(v___x_5507_);
                            v___x_5549_ = crate::leanh::lean_box(0);
                            v_isShared_5550_ = v_isSharedCheck_5554_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_declName_5497_);
                    v___f_5555_ = crate::leanh::lean_alloc_closure(
                        l_Lean_mkCasesOn___lam__0___boxed as *mut core::ffi::c_void,
                        7,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5555_, 0, v_declName_5497_);
                    v___x_5556_ = l_Lean_mkCasesOn___closed__2;
                    v___x_5557_ = l_Lean_mkCasesOn___closed__3;
                    v___x_5558_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_mkCasesOn___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_mkCasesOn___closed__6_once),
                        _init_l_Lean_mkCasesOn___closed__6,
                    );
                    v___x_5559_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5504_,
                        v_options_5503_,
                        v___x_5558_,
                    );
                    if v___x_5559_ == 0 {
                        v___x_5713_ = l_Lean_trace_profiler;
                        v___x_5714_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2(
                            v_options_5503_,
                            v___x_5713_,
                        );
                        if v___x_5714_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_5555_);
                            v___x_5715_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(v_declName_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
                            if crate::leanh::lean_obj_tag(v___x_5715_) == 0 {
                                v_a_5716_ = crate::leanh::lean_ctor_get(v___x_5715_, 0);
                                crate::leanh::lean_inc(v_a_5716_);
                                crate::leanh::lean_dec_ref_known(v___x_5715_, 1);
                                v___x_5717_ =
                                    l_Lean_addDecl(v_a_5716_, v___x_5714_, v_a_5500_, v_a_5501_);
                                if crate::leanh::lean_obj_tag(v___x_5717_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5717_, 1);
                                    crate::leanh::lean_inc(v_name_5506_);
                                    v___x_5718_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(v_name_5506_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
                                    crate::leanh::lean_dec_ref(v___x_5718_);
                                    v___x_5719_ = lean_st_ref_take(v_a_5501_);
                                    v_env_5720_ = crate::leanh::lean_ctor_get(v___x_5719_, 0);
                                    v_nextMacroScope_5721_ =
                                        crate::leanh::lean_ctor_get(v___x_5719_, 1);
                                    v_ngen_5722_ = crate::leanh::lean_ctor_get(v___x_5719_, 2);
                                    v_auxDeclNGen_5723_ =
                                        crate::leanh::lean_ctor_get(v___x_5719_, 3);
                                    v_traceState_5724_ =
                                        crate::leanh::lean_ctor_get(v___x_5719_, 4);
                                    v_messages_5725_ = crate::leanh::lean_ctor_get(v___x_5719_, 6);
                                    v_infoState_5726_ = crate::leanh::lean_ctor_get(v___x_5719_, 7);
                                    v_snapshotTasks_5727_ =
                                        crate::leanh::lean_ctor_get(v___x_5719_, 8);
                                    v_isSharedCheck_5753_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5719_)) as u8;
                                    if v_isSharedCheck_5753_ == 0 {
                                        v_unused_5754_ =
                                            crate::leanh::lean_ctor_get(v___x_5719_, 5);
                                        crate::leanh::lean_dec(v_unused_5754_);
                                        v___x_5729_ = v___x_5719_;
                                        v_isShared_5730_ = v_isSharedCheck_5753_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_snapshotTasks_5727_);
                                        crate::leanh::lean_inc(v_infoState_5726_);
                                        crate::leanh::lean_inc(v_messages_5725_);
                                        crate::leanh::lean_inc(v_traceState_5724_);
                                        crate::leanh::lean_inc(v_auxDeclNGen_5723_);
                                        crate::leanh::lean_inc(v_ngen_5722_);
                                        crate::leanh::lean_inc(v_nextMacroScope_5721_);
                                        crate::leanh::lean_inc(v_env_5720_);
                                        crate::leanh::lean_dec(v___x_5719_);
                                        v___x_5729_ = crate::leanh::lean_box(0);
                                        v_isShared_5730_ = v_isSharedCheck_5753_;
                                        state = 26;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_name_5506_);
                                    return v___x_5717_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_name_5506_);
                                v_a_5755_ = crate::leanh::lean_ctor_get(v___x_5715_, 0);
                                v_isSharedCheck_5762_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5715_)) as u8;
                                if v_isSharedCheck_5762_ == 0 {
                                    v___x_5757_ = v___x_5715_;
                                    v_isShared_5758_ = v_isSharedCheck_5762_;
                                    state = 30;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5755_);
                                    crate::leanh::lean_dec(v___x_5715_);
                                    v___x_5757_ = crate::leanh::lean_box(0);
                                    v_isShared_5758_ = v_isSharedCheck_5762_;
                                    state = 30;
                                    continue;
                                }
                            }
                        } else {
                            state = 17;
                            continue;
                        }
                    } else {
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_name_5506_);
                v___x_5523_ = l_Lean_markAuxRecursor(v_env_5512_, v_name_5506_);
                v___x_5524_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5521_, 5, v___x_5524_);
                    crate::leanh::lean_ctor_set(v___x_5521_, 0, v___x_5523_);
                    v___x_5526_ = v___x_5521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5544_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 1, v_nextMacroScope_5513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 2, v_ngen_5514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 3, v_auxDeclNGen_5515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 4, v_traceState_5516_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 5, v___x_5524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 6, v_messages_5517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 7, v_infoState_5518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 8, v_snapshotTasks_5519_);
                    v___x_5526_ = v_reuseFailAlloc_5544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5527_ = lean_st_ref_set(v_a_5501_, v___x_5526_);
                v___x_5528_ = lean_st_ref_take(v_a_5499_);
                v_mctx_5529_ = crate::leanh::lean_ctor_get(v___x_5528_, 0);
                v_zetaDeltaFVarIds_5530_ = crate::leanh::lean_ctor_get(v___x_5528_, 2);
                v_postponed_5531_ = crate::leanh::lean_ctor_get(v___x_5528_, 3);
                v_diag_5532_ = crate::leanh::lean_ctor_get(v___x_5528_, 4);
                v_isSharedCheck_5542_ = (!crate::leanh::lean_is_exclusive(v___x_5528_)) as u8;
                if v_isSharedCheck_5542_ == 0 {
                    v_unused_5543_ = crate::leanh::lean_ctor_get(v___x_5528_, 1);
                    crate::leanh::lean_dec(v_unused_5543_);
                    v___x_5534_ = v___x_5528_;
                    v_isShared_5535_ = v_isSharedCheck_5542_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5532_);
                    crate::leanh::lean_inc(v_postponed_5531_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5530_);
                    crate::leanh::lean_inc(v_mctx_5529_);
                    crate::leanh::lean_dec(v___x_5528_);
                    v___x_5534_ = crate::leanh::lean_box(0);
                    v_isShared_5535_ = v_isSharedCheck_5542_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5536_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5534_, 1, v___x_5536_);
                    v___x_5538_ = v___x_5534_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5541_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_mctx_5529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 1, v___x_5536_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5541_,
                        2,
                        v_zetaDeltaFVarIds_5530_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 3, v_postponed_5531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5541_, 4, v_diag_5532_);
                    v___x_5538_ = v_reuseFailAlloc_5541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5539_ = lean_st_ref_set(v_a_5499_, v___x_5538_);
                v___x_5540_ = l_Lean_enableRealizationsForConst(v_name_5506_, v_a_5500_, v_a_5501_);
                return v___x_5540_;
            }
            5 => {
                if v_isShared_5550_ == 0 {
                    v___x_5552_ = v___x_5549_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
                    v___x_5552_ = v_reuseFailAlloc_5553_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5552_;
            }
            7 => {
                v___x_5564_ = lean_io_mono_nanos_now();
                v___x_5565_ = lean_float_of_nat(v___y_5561_);
                v___x_5566_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_mkCasesOn___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_mkCasesOn___closed__7_once),
                    _init_l_Lean_mkCasesOn___closed__7,
                );
                v___x_5567_ = lean_float_div(v___x_5565_, v___x_5566_);
                v___x_5568_ = lean_float_of_nat(v___x_5564_);
                v___x_5569_ = lean_float_div(v___x_5568_, v___x_5566_);
                v___x_5570_ = crate::leanh::lean_box_float(v___x_5567_);
                v___x_5571_ = crate::leanh::lean_box_float(v___x_5569_);
                v___x_5572_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5572_, 0, v___x_5570_);
                crate::leanh::lean_ctor_set(v___x_5572_, 1, v___x_5571_);
                v___x_5573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5573_, 0, v_a_5563_);
                crate::leanh::lean_ctor_set(v___x_5573_, 1, v___x_5572_);
                v___x_5574_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3(v___x_5556_, v_hasTrace_5505_, v___x_5557_, v_options_5503_, v___x_5559_, v___y_5562_, v___f_5555_, v___x_5573_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
                return v___x_5574_;
            }
            8 => {
                v___x_5579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5579_, 0, v_a_5578_);
                v___y_5561_ = v___y_5576_;
                v___y_5562_ = v___y_5577_;
                v_a_5563_ = v___x_5579_;
                state = 7;
                continue;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v___y_5583_) == 0 {
                    v_a_5584_ = crate::leanh::lean_ctor_get(v___y_5583_, 0);
                    v_isSharedCheck_5591_ = (!crate::leanh::lean_is_exclusive(v___y_5583_)) as u8;
                    if v_isSharedCheck_5591_ == 0 {
                        v___x_5586_ = v___y_5583_;
                        v_isShared_5587_ = v_isSharedCheck_5591_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5584_);
                        crate::leanh::lean_dec(v___y_5583_);
                        v___x_5586_ = crate::leanh::lean_box(0);
                        v_isShared_5587_ = v_isSharedCheck_5591_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_a_5592_ = crate::leanh::lean_ctor_get(v___y_5583_, 0);
                    crate::leanh::lean_inc(v_a_5592_);
                    crate::leanh::lean_dec_ref_known(v___y_5583_, 1);
                    v___y_5576_ = v___y_5581_;
                    v___y_5577_ = v___y_5582_;
                    v_a_5578_ = v_a_5592_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v_isShared_5587_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5586_, 1);
                    v___x_5589_ = v___x_5586_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5584_);
                    v___x_5589_ = v_reuseFailAlloc_5590_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_5561_ = v___y_5581_;
                v___y_5562_ = v___y_5582_;
                v_a_5563_ = v___x_5589_;
                state = 7;
                continue;
            }
            12 => {
                v___x_5597_ = lean_io_get_num_heartbeats();
                v___x_5598_ = lean_float_of_nat(v___y_5595_);
                v___x_5599_ = lean_float_of_nat(v___x_5597_);
                v___x_5600_ = crate::leanh::lean_box_float(v___x_5598_);
                v___x_5601_ = crate::leanh::lean_box_float(v___x_5599_);
                v___x_5602_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5602_, 0, v___x_5600_);
                crate::leanh::lean_ctor_set(v___x_5602_, 1, v___x_5601_);
                v___x_5603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5603_, 0, v_a_5596_);
                crate::leanh::lean_ctor_set(v___x_5603_, 1, v___x_5602_);
                v___x_5604_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3(v___x_5556_, v_hasTrace_5505_, v___x_5557_, v_options_5503_, v___x_5559_, v___y_5594_, v___f_5555_, v___x_5603_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_);
                return v___x_5604_;
            }
            13 => {
                v___x_5609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5609_, 0, v_a_5608_);
                v___y_5594_ = v___y_5606_;
                v___y_5595_ = v___y_5607_;
                v_a_5596_ = v___x_5609_;
                state = 12;
                continue;
            }
            14 => {
                if crate::leanh::lean_obj_tag(v___y_5613_) == 0 {
                    v_a_5614_ = crate::leanh::lean_ctor_get(v___y_5613_, 0);
                    v_isSharedCheck_5621_ = (!crate::leanh::lean_is_exclusive(v___y_5613_)) as u8;
                    if v_isSharedCheck_5621_ == 0 {
                        v___x_5616_ = v___y_5613_;
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5614_);
                        crate::leanh::lean_dec(v___y_5613_);
                        v___x_5616_ = crate::leanh::lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_a_5622_ = crate::leanh::lean_ctor_get(v___y_5613_, 0);
                    crate::leanh::lean_inc(v_a_5622_);
                    crate::leanh::lean_dec_ref_known(v___y_5613_, 1);
                    v___y_5606_ = v___y_5611_;
                    v___y_5607_ = v___y_5612_;
                    v_a_5608_ = v_a_5622_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                if v_isShared_5617_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5616_, 1);
                    v___x_5619_ = v___x_5616_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5620_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
                    v___x_5619_ = v_reuseFailAlloc_5620_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_5594_ = v___y_5611_;
                v___y_5595_ = v___y_5612_;
                v_a_5596_ = v___x_5619_;
                state = 12;
                continue;
            }
            17 => {
                v___x_5624_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__1___redArg(v_a_5501_);
                v_a_5625_ = crate::leanh::lean_ctor_get(v___x_5624_, 0);
                crate::leanh::lean_inc(v_a_5625_);
                crate::leanh::lean_dec_ref(v___x_5624_);
                v___x_5626_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_5627_ =
                    l_Lean_Option_get___at___00Lean_mkCasesOn_spec__2(v_options_5503_, v___x_5626_);
                if v___x_5627_ == 0 {
                    v___x_5628_ = lean_io_mono_nanos_now();
                    v___x_5629_ =
                        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(
                            v_declName_5497_,
                            v_a_5498_,
                            v_a_5499_,
                            v_a_5500_,
                            v_a_5501_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5629_) == 0 {
                        v_a_5630_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
                        crate::leanh::lean_inc(v_a_5630_);
                        crate::leanh::lean_dec_ref_known(v___x_5629_, 1);
                        v___x_5631_ = l_Lean_addDecl(v_a_5630_, v___x_5627_, v_a_5500_, v_a_5501_);
                        if crate::leanh::lean_obj_tag(v___x_5631_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5631_, 1);
                            crate::leanh::lean_inc(v_name_5506_);
                            v___x_5632_ =
                                l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
                                    v_name_5506_,
                                    v_a_5498_,
                                    v_a_5499_,
                                    v_a_5500_,
                                    v_a_5501_,
                                );
                            crate::leanh::lean_dec_ref(v___x_5632_);
                            v___x_5633_ = lean_st_ref_take(v_a_5501_);
                            v_env_5634_ = crate::leanh::lean_ctor_get(v___x_5633_, 0);
                            v_nextMacroScope_5635_ = crate::leanh::lean_ctor_get(v___x_5633_, 1);
                            v_ngen_5636_ = crate::leanh::lean_ctor_get(v___x_5633_, 2);
                            v_auxDeclNGen_5637_ = crate::leanh::lean_ctor_get(v___x_5633_, 3);
                            v_traceState_5638_ = crate::leanh::lean_ctor_get(v___x_5633_, 4);
                            v_messages_5639_ = crate::leanh::lean_ctor_get(v___x_5633_, 6);
                            v_infoState_5640_ = crate::leanh::lean_ctor_get(v___x_5633_, 7);
                            v_snapshotTasks_5641_ = crate::leanh::lean_ctor_get(v___x_5633_, 8);
                            v_isSharedCheck_5667_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5633_)) as u8;
                            if v_isSharedCheck_5667_ == 0 {
                                v_unused_5668_ = crate::leanh::lean_ctor_get(v___x_5633_, 5);
                                crate::leanh::lean_dec(v_unused_5668_);
                                v___x_5643_ = v___x_5633_;
                                v_isShared_5644_ = v_isSharedCheck_5667_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snapshotTasks_5641_);
                                crate::leanh::lean_inc(v_infoState_5640_);
                                crate::leanh::lean_inc(v_messages_5639_);
                                crate::leanh::lean_inc(v_traceState_5638_);
                                crate::leanh::lean_inc(v_auxDeclNGen_5637_);
                                crate::leanh::lean_inc(v_ngen_5636_);
                                crate::leanh::lean_inc(v_nextMacroScope_5635_);
                                crate::leanh::lean_inc(v_env_5634_);
                                crate::leanh::lean_dec(v___x_5633_);
                                v___x_5643_ = crate::leanh::lean_box(0);
                                v_isShared_5644_ = v_isSharedCheck_5667_;
                                state = 18;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_name_5506_);
                            v___y_5581_ = v___x_5628_;
                            v___y_5582_ = v_a_5625_;
                            v___y_5583_ = v___x_5631_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_5506_);
                        v_a_5669_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
                        crate::leanh::lean_inc(v_a_5669_);
                        crate::leanh::lean_dec_ref_known(v___x_5629_, 1);
                        v___y_5576_ = v___x_5628_;
                        v___y_5577_ = v_a_5625_;
                        v_a_5578_ = v_a_5669_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___x_5670_ = lean_io_get_num_heartbeats();
                    v___x_5671_ =
                        l___private_Lean_Meta_Constructions_CasesOn_0__Lean_Meta_mkCasesOnDecl(
                            v_declName_5497_,
                            v_a_5498_,
                            v_a_5499_,
                            v_a_5500_,
                            v_a_5501_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5671_) == 0 {
                        v_a_5672_ = crate::leanh::lean_ctor_get(v___x_5671_, 0);
                        crate::leanh::lean_inc(v_a_5672_);
                        crate::leanh::lean_dec_ref_known(v___x_5671_, 1);
                        v___x_5673_ = 0;
                        v___x_5674_ = l_Lean_addDecl(v_a_5672_, v___x_5673_, v_a_5500_, v_a_5501_);
                        if crate::leanh::lean_obj_tag(v___x_5674_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5674_, 1);
                            crate::leanh::lean_inc(v_name_5506_);
                            v___x_5675_ =
                                l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(
                                    v_name_5506_,
                                    v_a_5498_,
                                    v_a_5499_,
                                    v_a_5500_,
                                    v_a_5501_,
                                );
                            crate::leanh::lean_dec_ref(v___x_5675_);
                            v___x_5676_ = lean_st_ref_take(v_a_5501_);
                            v_env_5677_ = crate::leanh::lean_ctor_get(v___x_5676_, 0);
                            v_nextMacroScope_5678_ = crate::leanh::lean_ctor_get(v___x_5676_, 1);
                            v_ngen_5679_ = crate::leanh::lean_ctor_get(v___x_5676_, 2);
                            v_auxDeclNGen_5680_ = crate::leanh::lean_ctor_get(v___x_5676_, 3);
                            v_traceState_5681_ = crate::leanh::lean_ctor_get(v___x_5676_, 4);
                            v_messages_5682_ = crate::leanh::lean_ctor_get(v___x_5676_, 6);
                            v_infoState_5683_ = crate::leanh::lean_ctor_get(v___x_5676_, 7);
                            v_snapshotTasks_5684_ = crate::leanh::lean_ctor_get(v___x_5676_, 8);
                            v_isSharedCheck_5710_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5676_)) as u8;
                            if v_isSharedCheck_5710_ == 0 {
                                v_unused_5711_ = crate::leanh::lean_ctor_get(v___x_5676_, 5);
                                crate::leanh::lean_dec(v_unused_5711_);
                                v___x_5686_ = v___x_5676_;
                                v_isShared_5687_ = v_isSharedCheck_5710_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snapshotTasks_5684_);
                                crate::leanh::lean_inc(v_infoState_5683_);
                                crate::leanh::lean_inc(v_messages_5682_);
                                crate::leanh::lean_inc(v_traceState_5681_);
                                crate::leanh::lean_inc(v_auxDeclNGen_5680_);
                                crate::leanh::lean_inc(v_ngen_5679_);
                                crate::leanh::lean_inc(v_nextMacroScope_5678_);
                                crate::leanh::lean_inc(v_env_5677_);
                                crate::leanh::lean_dec(v___x_5676_);
                                v___x_5686_ = crate::leanh::lean_box(0);
                                v_isShared_5687_ = v_isSharedCheck_5710_;
                                state = 22;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_name_5506_);
                            v___y_5611_ = v_a_5625_;
                            v___y_5612_ = v___x_5670_;
                            v___y_5613_ = v___x_5674_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_5506_);
                        v_a_5712_ = crate::leanh::lean_ctor_get(v___x_5671_, 0);
                        crate::leanh::lean_inc(v_a_5712_);
                        crate::leanh::lean_dec_ref_known(v___x_5671_, 1);
                        v___y_5606_ = v_a_5625_;
                        v___y_5607_ = v___x_5670_;
                        v_a_5608_ = v_a_5712_;
                        state = 13;
                        continue;
                    }
                }
            }
            18 => {
                crate::leanh::lean_inc(v_name_5506_);
                v___x_5645_ = l_Lean_markAuxRecursor(v_env_5634_, v_name_5506_);
                v___x_5646_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5644_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5643_, 5, v___x_5646_);
                    crate::leanh::lean_ctor_set(v___x_5643_, 0, v___x_5645_);
                    v___x_5648_ = v___x_5643_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5666_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 0, v___x_5645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 1, v_nextMacroScope_5635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 2, v_ngen_5636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 3, v_auxDeclNGen_5637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 4, v_traceState_5638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 5, v___x_5646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 6, v_messages_5639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 7, v_infoState_5640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 8, v_snapshotTasks_5641_);
                    v___x_5648_ = v_reuseFailAlloc_5666_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_5649_ = lean_st_ref_set(v_a_5501_, v___x_5648_);
                v___x_5650_ = lean_st_ref_take(v_a_5499_);
                v_mctx_5651_ = crate::leanh::lean_ctor_get(v___x_5650_, 0);
                v_zetaDeltaFVarIds_5652_ = crate::leanh::lean_ctor_get(v___x_5650_, 2);
                v_postponed_5653_ = crate::leanh::lean_ctor_get(v___x_5650_, 3);
                v_diag_5654_ = crate::leanh::lean_ctor_get(v___x_5650_, 4);
                v_isSharedCheck_5664_ = (!crate::leanh::lean_is_exclusive(v___x_5650_)) as u8;
                if v_isSharedCheck_5664_ == 0 {
                    v_unused_5665_ = crate::leanh::lean_ctor_get(v___x_5650_, 1);
                    crate::leanh::lean_dec(v_unused_5665_);
                    v___x_5656_ = v___x_5650_;
                    v_isShared_5657_ = v_isSharedCheck_5664_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5654_);
                    crate::leanh::lean_inc(v_postponed_5653_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5652_);
                    crate::leanh::lean_inc(v_mctx_5651_);
                    crate::leanh::lean_dec(v___x_5650_);
                    v___x_5656_ = crate::leanh::lean_box(0);
                    v_isShared_5657_ = v_isSharedCheck_5664_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_5658_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5657_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5656_, 1, v___x_5658_);
                    v___x_5660_ = v___x_5656_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5663_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_mctx_5651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 1, v___x_5658_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5663_,
                        2,
                        v_zetaDeltaFVarIds_5652_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 3, v_postponed_5653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 4, v_diag_5654_);
                    v___x_5660_ = v_reuseFailAlloc_5663_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_5661_ = lean_st_ref_set(v_a_5499_, v___x_5660_);
                v___x_5662_ = l_Lean_enableRealizationsForConst(v_name_5506_, v_a_5500_, v_a_5501_);
                v___y_5581_ = v___x_5628_;
                v___y_5582_ = v_a_5625_;
                v___y_5583_ = v___x_5662_;
                state = 9;
                continue;
            }
            22 => {
                crate::leanh::lean_inc(v_name_5506_);
                v___x_5688_ = l_Lean_markAuxRecursor(v_env_5677_, v_name_5506_);
                v___x_5689_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5686_, 5, v___x_5689_);
                    crate::leanh::lean_ctor_set(v___x_5686_, 0, v___x_5688_);
                    v___x_5691_ = v___x_5686_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5709_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 0, v___x_5688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 1, v_nextMacroScope_5678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 2, v_ngen_5679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 3, v_auxDeclNGen_5680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 4, v_traceState_5681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 5, v___x_5689_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 6, v_messages_5682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 7, v_infoState_5683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 8, v_snapshotTasks_5684_);
                    v___x_5691_ = v_reuseFailAlloc_5709_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_5692_ = lean_st_ref_set(v_a_5501_, v___x_5691_);
                v___x_5693_ = lean_st_ref_take(v_a_5499_);
                v_mctx_5694_ = crate::leanh::lean_ctor_get(v___x_5693_, 0);
                v_zetaDeltaFVarIds_5695_ = crate::leanh::lean_ctor_get(v___x_5693_, 2);
                v_postponed_5696_ = crate::leanh::lean_ctor_get(v___x_5693_, 3);
                v_diag_5697_ = crate::leanh::lean_ctor_get(v___x_5693_, 4);
                v_isSharedCheck_5707_ = (!crate::leanh::lean_is_exclusive(v___x_5693_)) as u8;
                if v_isSharedCheck_5707_ == 0 {
                    v_unused_5708_ = crate::leanh::lean_ctor_get(v___x_5693_, 1);
                    crate::leanh::lean_dec(v_unused_5708_);
                    v___x_5699_ = v___x_5693_;
                    v_isShared_5700_ = v_isSharedCheck_5707_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5697_);
                    crate::leanh::lean_inc(v_postponed_5696_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5695_);
                    crate::leanh::lean_inc(v_mctx_5694_);
                    crate::leanh::lean_dec(v___x_5693_);
                    v___x_5699_ = crate::leanh::lean_box(0);
                    v_isShared_5700_ = v_isSharedCheck_5707_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_5701_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5699_, 1, v___x_5701_);
                    v___x_5703_ = v___x_5699_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5706_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5706_, 0, v_mctx_5694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5706_, 1, v___x_5701_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5706_,
                        2,
                        v_zetaDeltaFVarIds_5695_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5706_, 3, v_postponed_5696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5706_, 4, v_diag_5697_);
                    v___x_5703_ = v_reuseFailAlloc_5706_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_5704_ = lean_st_ref_set(v_a_5499_, v___x_5703_);
                v___x_5705_ = l_Lean_enableRealizationsForConst(v_name_5506_, v_a_5500_, v_a_5501_);
                v___y_5611_ = v_a_5625_;
                v___y_5612_ = v___x_5670_;
                v___y_5613_ = v___x_5705_;
                state = 14;
                continue;
            }
            26 => {
                crate::leanh::lean_inc(v_name_5506_);
                v___x_5731_ = l_Lean_markAuxRecursor(v_env_5720_, v_name_5506_);
                v___x_5732_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
                if v_isShared_5730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5729_, 5, v___x_5732_);
                    crate::leanh::lean_ctor_set(v___x_5729_, 0, v___x_5731_);
                    v___x_5734_ = v___x_5729_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5752_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 0, v___x_5731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 1, v_nextMacroScope_5721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 2, v_ngen_5722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 3, v_auxDeclNGen_5723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 4, v_traceState_5724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 5, v___x_5732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 6, v_messages_5725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 7, v_infoState_5726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5752_, 8, v_snapshotTasks_5727_);
                    v___x_5734_ = v_reuseFailAlloc_5752_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_5735_ = lean_st_ref_set(v_a_5501_, v___x_5734_);
                v___x_5736_ = lean_st_ref_take(v_a_5499_);
                v_mctx_5737_ = crate::leanh::lean_ctor_get(v___x_5736_, 0);
                v_zetaDeltaFVarIds_5738_ = crate::leanh::lean_ctor_get(v___x_5736_, 2);
                v_postponed_5739_ = crate::leanh::lean_ctor_get(v___x_5736_, 3);
                v_diag_5740_ = crate::leanh::lean_ctor_get(v___x_5736_, 4);
                v_isSharedCheck_5750_ = (!crate::leanh::lean_is_exclusive(v___x_5736_)) as u8;
                if v_isSharedCheck_5750_ == 0 {
                    v_unused_5751_ = crate::leanh::lean_ctor_get(v___x_5736_, 1);
                    crate::leanh::lean_dec(v_unused_5751_);
                    v___x_5742_ = v___x_5736_;
                    v_isShared_5743_ = v_isSharedCheck_5750_;
                    state = 28;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5740_);
                    crate::leanh::lean_inc(v_postponed_5739_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5738_);
                    crate::leanh::lean_inc(v_mctx_5737_);
                    crate::leanh::lean_dec(v___x_5736_);
                    v___x_5742_ = crate::leanh::lean_box(0);
                    v_isShared_5743_ = v_isSharedCheck_5750_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_5744_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
                if v_isShared_5743_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5742_, 1, v___x_5744_);
                    v___x_5746_ = v___x_5742_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5749_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_mctx_5737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5749_, 1, v___x_5744_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5749_,
                        2,
                        v_zetaDeltaFVarIds_5738_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5749_, 3, v_postponed_5739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5749_, 4, v_diag_5740_);
                    v___x_5746_ = v_reuseFailAlloc_5749_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_5747_ = lean_st_ref_set(v_a_5499_, v___x_5746_);
                v___x_5748_ = l_Lean_enableRealizationsForConst(v_name_5506_, v_a_5500_, v_a_5501_);
                return v___x_5748_;
            }
            30 => {
                if v_isShared_5758_ == 0 {
                    v___x_5760_ = v___x_5757_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5761_, 0, v_a_5755_);
                    v___x_5760_ = v_reuseFailAlloc_5761_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5760_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOn___boxed(
    mut v_declName_5763_: *mut crate::leanh::LeanObject,
    mut v_a_5764_: *mut crate::leanh::LeanObject,
    mut v_a_5765_: *mut crate::leanh::LeanObject,
    mut v_a_5766_: *mut crate::leanh::LeanObject,
    mut v_a_5767_: *mut crate::leanh::LeanObject,
    mut v_a_5768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5769_ = l_Lean_mkCasesOn(v_declName_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_);
    crate::leanh::lean_dec(v_a_5767_);
    crate::leanh::lean_dec_ref(v_a_5766_);
    crate::leanh::lean_dec(v_a_5765_);
    crate::leanh::lean_dec_ref(v_a_5764_);
    return v_res_5769_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0(
    mut v_declName_5770_: *mut crate::leanh::LeanObject,
    mut v_s_5771_: u8,
    mut v___y_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
    mut v___y_5774_: *mut crate::leanh::LeanObject,
    mut v___y_5775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5777_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_5770_, v_s_5771_, v___y_5773_, v___y_5775_);
    return v___x_5777_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(
    mut v_declName_5778_: *mut crate::leanh::LeanObject,
    mut v_s_5779_: *mut crate::leanh::LeanObject,
    mut v___y_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_boxed_5785_: u8 = 0;
    let mut v_res_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_5785_ = (crate::leanh::lean_unbox(v_s_5779_) as u8);
    v_res_5786_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0(v_declName_5778_, v_s_boxed_5785_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
    crate::leanh::lean_dec(v___y_5783_);
    crate::leanh::lean_dec_ref(v___y_5782_);
    crate::leanh::lean_dec(v___y_5781_);
    crate::leanh::lean_dec_ref(v___y_5780_);
    return v_res_5786_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6(
    mut v_00_u03b1_5787_: *mut crate::leanh::LeanObject,
    mut v_x_5788_: *mut crate::leanh::LeanObject,
    mut v___y_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5794_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___redArg(v_x_5788_);
    return v___x_5794_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6___boxed(
    mut v_00_u03b1_5795_: *mut crate::leanh::LeanObject,
    mut v_x_5796_: *mut crate::leanh::LeanObject,
    mut v___y_5797_: *mut crate::leanh::LeanObject,
    mut v___y_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5802_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__3_spec__6(v_00_u03b1_5795_, v_x_5796_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_);
    crate::leanh::lean_dec(v___y_5800_);
    crate::leanh::lean_dec_ref(v___y_5799_);
    crate::leanh::lean_dec(v___y_5798_);
    crate::leanh::lean_dec_ref(v___y_5797_);
    return v_res_5802_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: u8 = 0;
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5863_ = l_Lean_mkCasesOn___closed__2;
    v___x_5864_ = 0;
    v___x_5865_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_;
    v___x_5866_ = l_Lean_registerTraceClass(v___x_5863_, v___x_5864_, v___x_5865_);
    return v___x_5866_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(
    mut v_a_5867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5868_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
    return v_res_5868_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_CasesOn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_AddDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_CasesOn(
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
pub unsafe fn initialize_Lean_Meta_Constructions_CasesOn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_AddDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CasesOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_CasesOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_CasesOn(builtin);
}
